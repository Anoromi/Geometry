import Geometry.Quadrilateral

variable (q: Quadrilateral)
variable (cq: ConvexQuadrilateral)

axiom rectangle_area (r: Rectangle cq) : ℝ
axiom rectangle_area_eq (r: Rectangle cq) : rectangle_area cq r = cq.q.side1.length * cq.q.side2.length
