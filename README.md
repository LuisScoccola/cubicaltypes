# cubicaltypes

### CubicalType.v

- Definition of 1,2,3-semicubical types (cubical type or CT).
- Definition of morphisms between cubical types.
- Characterization of identity types of 1 and 2 cubical types.
- Some basic operations on cubical types (flip (aka op), higher dimensional flips, ...)

### CubicalTypeExamples.v

- Interval cubical type.
- Singular cubical type induced by a type.
- Singular cubical type induced by the universe.
- Some operations on squares and cubes in the universe (whiskerings, degenerate cubes, ...)

### CubicalTypeProduct.v

- Definition of product 1CT x 1CT -> 2CT and 1CT x 2CT -> 3CT.
- Proof that the 1x1-product is (anti)commutative (needed for the commutativity of (co)lims).

### CubicalTypeExponential.v

- Definition of exponential cubical type H^C, that has as 0-cubes the maps C -> H and as 1-cubes the natural transformations. This is defined for H : 2CT and C : 1CT or H : 3CT and C : 2CT.

### CubicalTypeDiagram.v

- Definition of diagrams indexed by 1,2,3-CT.
- Definition of diagram morphisms.
- Composition of diagram morphisms.
- Cone of 1-diagram, cone of 2-diagram.
- Cone of a 2-diagram over a product CxD, in the "category" of C-diagrams (needed to define the partial (co)lim_D F : D -> Type, for a functor F : C x D -> Type). 
- Definition of universal cone for 1-diagrams, and 2-diagrams.
