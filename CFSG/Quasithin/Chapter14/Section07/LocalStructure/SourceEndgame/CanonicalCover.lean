module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ElementaryQuotient
public import Theory.Representation.BinaryConjugationSection.Canonical
public import Theory.Representation.BinaryConjugationSection.Projection

/-!
# The canonical Ru2 action from the original conjugate roots

Starting with the recognized natural P/(S∩Sᵏ) section, the root generation
and Frattini bounds prove that P/U is elementary. Its literal quotient
then carries the full H/P≃S₅ conjugation representation. The original
natural coordinates descend to an intertwining projection; its kernel is
E/U, with E=S∩Sᵏ, and the group commutator bound proves that kernel fixed.
The genuine Sylow SP proves commutator generation. Thus the original
six-dimensional indecomposable RuTwo fields are constructed without an
input representation on P/U, a projection witness or indecomposability.

The remaining source obligations are explicit: the natural P/E recognition,
the root-generation and Frattini statements, |E/U|=4, the Sylow SP, the
natural U/Z(T) action, and the local identifications P=O₂(H), H=C_G(Z(T)).
This conditional application does not assert the full 14.7.71–74 conclusions.
Their proof and the RuOne record remain with the local endgame owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.73–75 and Ru2 in J.1, printed pp.1076–1078 and 431.
-/

public section

open Subgroup Representation Representation.SL2FourNatural Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open ChapterJ

variable {G : Type*} [Group G] [Finite G]

/-- Construct Ru2 directly from the conjugate roots and the recognized natural P/E section. -/
theorem exists_ruTwo_of_source_roots
    (V : Subgroup G) (T : Sylow 2 G) (K S : Subgroup G) [Group.IsPerfect K]
    (hKH : K ≤ centralizerOfSylowCenter T) (hSK : S ≤ K)
    (qH : centralizerOfSylowCenter T →* S5)
    (hq : Function.Surjective qH)
    (hqker : qH.ker = ((centralizerOfSylowCenter T).pCoreIn 2).subgroupOf
      (centralizerOfSylowCenter T))
    (a : L2FourAction)
    (dn : BinaryConjugationSection (centralizerOfSylowCenter T)
      (conjugateSpan (centralizerOfSylowCenter T) V) (sylowCenter T) (a.action.comp qH))
    (k : K) (qK : K →* SL) (hqK : Function.Surjective qK)
    (hmark : ∀ k : K, qH ⟨k, hKH k.property⟩ = alternatingActor a (qK k))
    (n : BinaryConjugationSection K ((centralizerOfSylowCenter T).pCoreIn 2)
      (S ⊓ S.conjBy ((k : G)⁻¹)) (naturalRepresentation.comp qK))
    (hUE : conjugateSpan (centralizerOfSylowCenter T) V ≤ S ⊓ S.conjBy ((k : G)⁻¹))
    (hS : IsPGroup 2 S)
    (hPhi : (frattini S).map S.subtype ≤ conjugateSpan (centralizerOfSylowCenter T) V)
    (hKgen : K = S ⊔ S.conjBy ((k : G)⁻¹))
    (hPgen : (centralizerOfSylowCenter T).pCoreIn 2 =
      (S ⊓ (centralizerOfSylowCenter T).pCoreIn 2) ⊔
      (S.conjBy ((k : G)⁻¹) ⊓ (centralizerOfSylowCenter T).pCoreIn 2))
    (hcard : (conjugateSpan (centralizerOfSylowCenter T) V).relIndex
      (S ⊓ S.conjBy ((k : G)⁻¹)) = 4)
    (R : Sylow 2 K)
    (hR : (R : Subgroup K).map K.subtype = S ⊔ (centralizerOfSylowCenter T).pCoreIn 2) :
    Nonempty (RuTwo V T) := by
  let H := centralizerOfSylowCenter T
  let P := H.pCoreIn 2
  let U := conjugateSpan H V
  let E := S ⊓ S.conjBy ((k : G)⁻¹)
  have hNP : H ≤ normalizer P := by
    apply (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 H)).mp
    rw [← hqker]
    infer_instance
  have hNU : H ≤ normalizer U := dn.normalized
  have hUP : U ≤ P := hUE.trans n.kernel_le
  let : (U.subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 H).trans hNU)
  let : (P.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer (hKH.trans hNP)
  let : (U.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer (hKH.trans hNU)
  obtain ⟨hEC, helem⟩ := elementary_source_quotient K P S U k qK hqK n hS hPhi
    (hKH.trans hNU) hKgen hPgen
  let : IsElementaryAbelian 2 (P ⧸ U.subgroupOf P) := helem
  obtain ⟨σ, d, hcoordinates⟩ := BinaryConjugationSection.exists_canonical H P U
    (pCoreIn_le 2 H) hUP hNP hNU qH hq hqker
  obtain ⟨p, hp, hpn, hpk⟩ := BinaryConjugationSection.exists_projection H K P U E
    hKH hUE qH qK hqK (alternatingActor a) hmark σ naturalRepresentation d n
  have hfix : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)) := by
    intro w hw g
    obtain ⟨x, rfl⟩ := hqK g
    have hwe : w ∈ d.imageSpace E := hpk ▸ hw
    have hc := d.fixed_on_imageSpace_of_commutator_le K E
      (by rwa [commutator_comm]) ⟨x, hKH x.property⟩ x.property w hwe
    change σ (qH ⟨x, hKH x.property⟩) w = w at hc
    change σ (alternatingActor a (qK x)) w = w
    rwa [hmark] at hc
  have hpkcard : Nat.card p.toLinearMap.ker = 4 := by
    rw [hpk]
    change Nat.card ((E.subgroupOf P).map d.coordinates) = 4
    rw [← relIndex_ker, d.kernel_eq, relIndex_subgroupOf n.kernel_le]
    exact hcard
  exact exists_ruTwo_of_source_sylow V T K S hKH n.section_le hSK qH hq hqker
    a dn σ d qK hmark p hp hfix hpkcard R hR
    (derived_le_of_frattini_image_le hS hPhi)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
