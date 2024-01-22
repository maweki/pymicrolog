from ev3dev2.motor import LargeMotor, OUTPUT_B, OUTPUT_C
from ev3dev2.sensor.lego import UltrasonicSensor
from pymicrolog import *
import operator

i1 = UltrasonicSensor()
m1 = LargeMotor(OUTPUT_B)
m2 = LargeMotor(OUTPUT_C)

# because the reading is programmed as an attribute, we have to create a closure
sensor_get_value = call((lambda i: i.distance_centimeters))
# we also have to create a closure to map named arguments to positional arguments
tacho_go = call((lambda m, s: m.run_forever(speed_sp=s)))
D = variable("D")

rules = [
    sensor_get_value(i1)@NEXT,

    tacho_go(m1, -100)@NEXT <= sensor_get_value(i1, D) & (D < 30),
    tacho_go(m2,  100)@NEXT <= sensor_get_value(i1, D) & (D < 30),
    tacho_go(m1, 100)@NEXT <= sensor_get_value(i1, D) & (D > 30),
    tacho_go(m2, 100)@NEXT <= sensor_get_value(i1, D) & (D > 30),
]

p = Program(rules)
p.run_cb(cycles=1000, cb=print)

m1.stop()
m2.stop()
