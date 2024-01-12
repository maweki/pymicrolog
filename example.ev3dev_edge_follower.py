from ev3dev2.motor import LargeMotor, OUTPUT_B, OUTPUT_C
from ev3dev2.sensor import INPUT_1
from ev3dev2.sensor.lego import ColorSensor
from pymicrolog import *
import operator

i1 = ColorSensor(INPUT_1)
m1 = LargeMotor(OUTPUT_B)
m2 = LargeMotor(OUTPUT_C)

# because the reading is programmed as an attribute, we have to create a closure
sensor_get_value = call((lambda i: i.reflected_light_intensity))
# we also have to create a closure to map named arguments to positional arguments
tacho_go = call((lambda m, s: m.run_forever(speed_sp=s)))
lightval = relation("lightval")
onLine = relation("online")
lt = oracle(operator.lt)
L = variable("L")

console_out = call(print)

rules = [
    sensor_get_value(i1)@NEXT,
    lightval(L) <= sensor_get_value(i1, L),
    onLine() <= lightval(L) & lt(L, 20), # can be written as (L < 20)
    console_out(L)@NEXT <= lightval(L),

    tacho_go(m1, 50)@NEXT <= onLine(),
    tacho_go(m2, 200)@NEXT <= onLine(),
    tacho_go(m1, 200)@NEXT <= ~onLine(),
    tacho_go(m2, 50)@NEXT <= ~onLine(),
]

p = Program(rules)
p.run_cb(cycles=1000, cb=print)

m1.stop()
m2.stop()
