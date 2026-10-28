module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeFixedTorus
public import Theory.Mathieu.M22.CentralCover.HexadPerfect
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary

/-!
# The full stabilizer of a Sylow-fixed M22 code vector

The nonzero fixed vector supplied by `CodeFixedTorus` is a hexad vector.
Its stabilizer is exactly the native hexad stabilizer, in both directions.
The actual six-point action identifies the quotient by the full two-core
with A₆. The original-centralizer application is in `M22CodeCentralizer`;
central covering kernels above this native group are retained there.
Transfer at the hexad index 77 also proves perfectness of its full preimage
in any finite perfect central cover: the actual kernel order divides 12.
This supplies the comparison of the printed two-residual with the perfect
residual in the original point centralizer.

Source: Aschbacher--Smith H.13, I.1.3(4) and 8.2.2(1), printed pp.395,407,715,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
open PerfectCentralCovering
namespace MathieuCode.NormalizedShadowRows

/-- The stabilizer of the code vector is the full native hexad stabilizer. -/
theorem code_hexad_vector_fixed_iff {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (g : M22) :
    m22CodeRepresentation g (m22HexadVector hB) = m22HexadVector hB ↔
      g ∈ MulAction.stabilizer M22 B := by
  refine ⟨hexad_vector_stabilizer hB g, ?_⟩
  intro hg
  apply Subtype.ext
  apply (SectionAction.octadVector_fixed_iff (m22Octad hB) (m22Embedding g)).mpr
  apply MulAction.mem_stabilizer_finset'.mpr
  intro i hi
  rcases (mem_m22AugmentedOctad B i).mp hi with rfl | rfl | ⟨j,hj,rfl⟩
  · exact (mem_m22AugmentedOctad B _).mpr (Or.inl (m22Embedding_fixed_zero g))
  · exact (mem_m22AugmentedOctad B _).mpr (Or.inr (Or.inl (m22Embedding_fixed_nine g)))
  · change (m22Embedding g).val (m22Coordinates j) ∈ m22AugmentedOctad B
    rw [m22Embedding_apply]
    exact (mem_m22AugmentedOctad B _).mpr
      (Or.inr (Or.inr ⟨g • j,MulAction.mem_stabilizer_finset'.mp hg hj,rfl⟩))

/-- The actual hexad quotient removes precisely its two-core. -/
def code_hexad_core_equiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (MulAction.stabilizer M22 B ⧸ pCore 2 (MulAction.stabilizer M22 B)) ≃*
      alternatingGroup (Fin 6) := by
  let K := (m22SetAction B).ker
  let e := m22HexadQuotientAlternatingEquiv hB
  let f := e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact (m22HexadKernel_elementaryAbelian hB).isPGroup 2 _
  have hbot : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    rcases (inferInstance : (pCore 2 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · have hp : IsPGroup 2 (alternatingGroup (Fin 6)) :=
        pCore_isPGroup.of_equiv ((MulEquiv.subgroupCongr he).trans topEquiv)
      let : Group.IsNilpotent (alternatingGroup (Fin 6)) := hp.isNilpotent
      let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance).elim
  exact (f.pCoreQuotientEquiv hf hk).trans
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
/-- The full hexad preimage in a perfect central cover remains perfect.
The index 77 is coprime to the actual covering kernel, whose order divides 12. -/
theorem code_hexad_preimage_perfect {Y : Type*} [Group Y] [Finite Y]
    (f : Cover Y M22) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Group.IsPerfect ((MulAction.stabilizer M22 B).comap f.toMonoidHom) := by
  let S := MulAction.stabilizer M22 B
  let P := S.comap f.toMonoidHom
  let q : P →* S := f.toMonoidHom.subgroupComap S
  let : Group.IsPerfect Y := f.isPerfect
  let : Group.IsPerfect S := m22HexadStabilizer_isPerfect hB
  have hq : Function.Surjective q :=
    f.toMonoidHom.subgroupComap_surjective_of_surjective S f.surjective
  have hi : P.index = 77 := by
    rw [index_comap_of_surjective S f.surjective]
    have hc := S.card_mul_index
    rw [m22Hexad_stabilizer_card hB,m22_order] at hc
    omega
  have hker : q.ker ≤ commutator P := by
    intro x hx
    have hfx : f.toMonoidHom (x : Y) = 1 := congrArg Subtype.val hx
    have hz := f.ker_le_center hfx
    have ht := MonoidHom.transfer_eq_pow (H := P) (Abelianization.of : P →* Abelianization P)
      (x : Y) (fun i g _ => by
        rw [mem_center_iff.mp (pow_mem hz i) g⁻¹,mul_assoc,inv_mul_cancel,mul_one])
    have hv : MonoidHom.transfer (Abelianization.of : P →* Abelianization P) (x : Y) = 1 :=
      Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
    have hm : x ^ P.index ∈ commutator P := by
      rw [←Abelianization.ker_of]
      exact ht.symm.trans hv
    have hd : orderOf x ∣ 12 := by
      have hd := (orderOf_dvd_natCard (⟨x,hfx⟩ : f.toMonoidHom.ker)).trans
        (M22UniversalMultiplier.kernel_card_dvd_twelve f)
      have he : orderOf (⟨x,hfx⟩ : f.toMonoidHom.ker) = orderOf x :=
        (orderOf_coe _).symm.trans (orderOf_coe x)
      exact he ▸ hd
    have hc : P.index.Coprime (orderOf x) := by
      rw [hi]
      exact (by decide : Nat.Coprime 77 12).of_dvd_right hd
    obtain ⟨m,hm'⟩ := exists_pow_eq_self_of_coprime hc
    exact hm' ▸ (commutator P).pow_mem hm m
  exact ⟨(sup_of_le_right hker).symm.trans
    (CentralExtension.ker_sup_commutator_eq_top_of_surjective q hq)⟩
end MathieuCode.NormalizedShadowRows
