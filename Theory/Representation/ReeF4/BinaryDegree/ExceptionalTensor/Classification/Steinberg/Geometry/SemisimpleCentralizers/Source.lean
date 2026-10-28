module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.SemisimpleTransport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.ToralConnectedness

/-!
# Connected semisimple F4 centralizers and actual Ree fusion

The complete toral centralizer proof, including the actual integral F4
stabilizer calculation, combines with torus placement and conjugation to give
connectedness for every semisimple point. Lang correction proves that ambient
conjugacy of odd-order points descends to both the whole Ree fixed group and
the original finite model. All geometric inputs are instantiated here.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §§3.9 and 12.5.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
theorem pointCentralizer_isConnected_of_semisimple (s : PointGroup F)
    (hs : IsSemisimpleElement (F4Chevalley.Carrier (k:=F)) s) :
    Variety.IsConnected (pointCentralizer s).carrierVariety :=
  connected_of_toral_source pointCentralizer_isConnected_of_mem_torus s hs

theorem model_pointCentralizer_isConnected (m : ℕ) (f : CoefficientField m →+* F)
    (x : Model m) (hx : ¬ 2 ∣ orderOf x) :
    Variety.IsConnected (pointCentralizer (modelEmbedding f x)).carrierVariety :=
  model_connected_of_toral_source pointCentralizer_isConnected_of_mem_torus m f x hx

theorem isConj_model_of_odd_order (m : ℕ) (f : CoefficientField m →+* F)
    (x y : Model m) (hx : ¬ 2 ∣ orderOf x)
    (hxy : IsConj (modelEmbedding f x) (modelEmbedding f y)) : IsConj x y :=
  isConj_model_of_toral_source pointCentralizer_isConnected_of_mem_torus m f x y hx hxy

theorem isConj_fixed_of_odd_order (m : ℕ) (x y : SourceFixedPoints.fixedGroup (F:=F) m)
    (hx : ¬ 2 ∣ orderOf x) (hxy : IsConj (x : PointGroup F) (y : PointGroup F)) : IsConj x y :=
  isConj_fixed_of_toral_source pointCentralizer_isConnected_of_mem_torus m x y hx hxy
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
