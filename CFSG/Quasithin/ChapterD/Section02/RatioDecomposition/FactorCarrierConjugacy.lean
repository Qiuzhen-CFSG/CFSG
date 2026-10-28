module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ConjugateFactors
/-!
# Carrier isomorphisms along literal factor conjugacy

An ambient conjugation between the embedded factor actors induces an
isomorphism of their original carriers. The range equivalences preserve the
literal factor inclusions. This transports the chosen S3 endpoint throughout
its support orbit in 15.1.2, printed p.1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
noncomputable def factorCarrierEquivOfConjugate {i j : d.Index} (g : G)
    (h : (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d j).actor) : (d.factor i).Carrier ≃* (d.factor j).Carrier :=
  (MonoidHom.ofInjective (c.ambientFactor d i).embedding.group_injective).trans
    ((Subgroup.equivMapOfInjective (c.ambientFactor d i).actor
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      ((MulEquiv.subgroupCongr h).trans
        (MonoidHom.ofInjective (c.ambientFactor d j).embedding.group_injective).symm))
end CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
