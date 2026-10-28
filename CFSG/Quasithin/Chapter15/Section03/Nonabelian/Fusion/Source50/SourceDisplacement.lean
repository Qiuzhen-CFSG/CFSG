module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.NonabelianBranch
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Displacement

/-!
# The source 53 commutator supplies the source 57 linear inputs

The actual U-image is the other Klein four-group in the orthogonal actor.
Its order-eight commutator is exactly V∩U. Dividing by the marked central
line gives the two-dimensional displacement of the generator of V*.
All images use the original projections U→U/Z and H→H/O₂(H).

Source: Aschbacher–Smith, 15.3.53(2) and 15.3.57(2), pp.1146,1148.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
variable {G : Type*} [Group G] [Finite G]

 theorem source_displacement_fields (d : CharacteristicTwo.LocalData G)
    (h : (localSetup d (centralizerH d.Z)).Hypothesis)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient d.Z d.ZS)]
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (hu : ¬ IsMulCommutative (closureU d.Z d.ZS))
    (hk : (quotientAction d.Z d.ZS).ker = pCore 2 (centralizerH d.Z))
    (v : ActorQuotient d.Z) (hv : zpowers v=CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.actorImage d.Z d.V) :
    LinearMap.range (actorRepresentation d.Z d.ZS hk v-LinearMap.id) =
        LocalRestrictions.vectorSubspace d.Z d.ZS (d.V ⊓ closureU d.Z d.ZS) ∧
      Module.finrank (ZMod 2)
        (LinearMap.range (actorRepresentation d.Z d.ZS hk v-LinearMap.id))=2 := by
  have hi := (nonabelian_intersections d (centralizerH d.Z) h hf hnon hu).2.1
  refine ⟨?_,?_⟩
  · rw [displacement_eq_vectorSubspace d.Z d.ZS hk d.V h.V_le_H v hv,hi]
  · exact displacement_rank_of_card d.Z d.ZS hk d.V h.V_le_H v hv
      (commutator_quotient_card d (centralizerH d.Z) h hf hnon hu)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
