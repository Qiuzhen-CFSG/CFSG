module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowLineCubic
public import Theory.GroupTheory.CoprimeQuotientSubgroups.ElementLift

/-!
# An intrinsic cubic on the original tensor line

The first tensor factor contains a cubic preserving and moving the common
Sylow fixed line. The original quotient L → SL₂(4) lifts this cubic through
its 2-core, retaining exponent three. Faithful original module coordinates
then transport preservation and movement to the literal tensor line.

Source: the cubic irreducibility step in Aschbacher–Smith 9.3.6.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem exists_tensorLine_cubic :
    ∃ d : G, d ∈ L ∧ d ^ 3 = 1 ∧
      d ∈ normalizer (m.tensorLine : Set G) ∧
      d ∉ centralizer (m.tensorLine : Set G) := by
  obtain ⟨P,hP⟩ := m.exists_tensorLine_coordinates_sylow
  obtain ⟨a,ha3,han,⟨v,hv,hav⟩⟩ := Binary.exists_first_cubic_on_sylow_line P
  let q : L →* SL2FourNatural.SL :=
    (e.trans m.firstMarking).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    (e.trans m.firstMarking).surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ (e.trans m.firstMarking).injective,
      QuotientGroup.ker_mk']
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [hk,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨d,hdq,hd3⟩ := exists_prime_exponent_lift q hq hcop a ha3
  let d0 : localOrbit T L := ⟨d,le_componentOrbit L T d.property⟩
  have hd0 : m.quotient d0 = (a,1) :=
    (m.first_factor d).trans (by change (q d,1) = (a,1); rw [hdq])
  have he (w : D.fullModule) :
      (m.sectionData.coordinates ⟨(d : G)*w*(d : G)⁻¹,
        (mem_normalizer_iff.mp (m.sectionData.normalized d0.property) w).mp w.property⟩).toAdd =
      Binary.action (a,1) (m.sectionData.coordinates w).toAdd := by
    have hh := m.sectionData.equivariant d0 w
    change (m.sectionData.coordinates _).toAdd =
      Binary.action (m.quotient d0) (m.sectionData.coordinates w).toAdd at hh
    rw [hd0] at hh
    exact hh
  have himg (w : D.fullModule) :
      (m.sectionData.coordinates w).toAdd ∈ m.sectionData.imageSpace m.tensorLine ↔
        (w : G) ∈ m.tensorLine := by
    constructor
    · intro hw
      obtain ⟨u,hu,heu⟩ := (m.sectionData.mem_imageSpace_iff _ _).mp hw
      have heuw := m.coordinates_injective (Multiplicative.toAdd.injective heu)
      exact heuw ▸ hu
    · intro hw
      exact (m.sectionData.mem_imageSpace_iff _ _).mpr ⟨w,hw,rfl⟩
  refine ⟨d,d.property,congrArg Subtype.val hd3,?_,?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨w,hw,rfl⟩
      let wV : D.fullModule := ⟨w,m.tensorLine_le_fullModule hw⟩
      apply (himg ⟨(d : G)*w*(d : G)⁻¹,
        (mem_normalizer_iff.mp (m.sectionData.normalized d0.property) w).mp wV.property⟩).mp
      rw [he wV,hP]
      exact han _ (hP ▸ (himg wV).mpr hw)
    · rw [card_map_of_injective (MulAut.conj (d : G)).injective]
  · intro hc
    obtain ⟨w,hw,hwv⟩ := (m.sectionData.mem_imageSpace_iff _ _).mp (hP.symm ▸ hv)
    apply hav
    rw [←hwv,←he]
    congr 2
    apply Subtype.ext
    change (d : G)*(w : G)*(d : G)⁻¹ = (w : G)
    rw [←hc w hw,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
