from pymicrolog import *

onLine = relation("online")
V, D = variables(*"VD")
config = call("config")

# because the reading is programmed as an attribute, we have to create a closure
sensor_get_value = call((lambda i: i.reflected_light_intensity))
# we also have to create a closure to map named arguments to positional arguments
tacho_go = call((lambda m, s: m.run_forever(speed_sp=s)))

p = Program([
    config()@NEXT,
    sensor_get_value(D)@NEXT <= config(..., ..., D),
    onLine() <= sensor_get_value(..., V) & (V < 20),

    tacho_go(D, 50)@NEXT <= onLine() & config(D, ..., ...),
    tacho_go(D, 200)@NEXT <= onLine() & config(..., D, ...),
    tacho_go(D, 200)@NEXT <= ~onLine() & config(D, ..., ...),
    tacho_go(D, 50)@NEXT <= ~onLine() & config(..., D, ...),
])

from ev3dev2.motor import LargeMotor, OUTPUT_B, OUTPUT_C
from ev3dev2.sensor import INPUT_1
from ev3dev2.sensor.lego import ColorSensor
i1 = ColorSensor(INPUT_1)
m1 = LargeMotor(OUTPUT_B)
m2 = LargeMotor(OUTPUT_C)

p.run_cb(cycles=1000, cb=print, fnmapping={"config": lambda : (m1, m2, i1)})

m1.stop()
m2.stop()
