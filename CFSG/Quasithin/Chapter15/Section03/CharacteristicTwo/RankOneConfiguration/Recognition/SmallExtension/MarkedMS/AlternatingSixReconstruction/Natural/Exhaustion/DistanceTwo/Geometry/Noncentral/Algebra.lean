module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Transposition.Source

/-!
# Noncentrality of a normal plane orbit

If a plane orbit is central modulo Z, the residual and edge supplement
put that orbit inside YZ. The normal closure N of the opposite layer's
intersection with the two-core then centralizes Y. A displacement bound
puts [N,E] inside Y. Normal generation and residual idempotence force the
whole core into Z, contradicting the contrary branch.

The displacement premise is proved on the actual whole cover in
Noncentral.Source; this algebraic lemma does not assume plane equality.
Source: MS93 (3.6), printed p.871, the first symplectic orbit paragraph.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral

private theorem residual_detection {M : Type*} [Group M]
    (hnormal : ∀ (N : Subgroup M) [N.Normal],
      (¬ N ≤ pCore 2 M) → pResidual 2 M ≤ N)
    (D N E : Subgroup M) [D.Normal] [N.Normal]
    (hE : ¬ E ≤ pCore 2 M) (hcomm : ⁅D,E⁆ ≤ N) :
    ⁅D,pResidual 2 M⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let C := (centralizer (D.map q : Set (M ⧸ N))).comap q
  have hC (A : Subgroup M) : A ≤ C ↔ ⁅D,A⁆ ≤ N := by
    change A ≤ (centralizer (D.map q : Set (M ⧸ N))).comap q ↔ _
    rw [←map_le_iff_le_comap,←le_centralizer_iff,
      ←commutator_eq_bot_iff_le_centralizer,←map_commutator,
      Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  let : (D.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hEC : E ≤ C := (hC E).mpr hcomm
  exact (hC (pResidual 2 M)).mp (hnormal C (fun h => hE (hEC.trans h)))

/-- The source's first noncentrality argument, with the finite whole-cover
calculation isolated as its literal displacement premise. -/
theorem normal_orbit_noncentral {M : Type*} [Group M] [Finite M]
    (T Z E Y : Subgroup M) [Z.Normal] [IsMulCommutative E]
    (hnormal : ∀ (N : Subgroup M) [N.Normal],
      (¬ N ≤ pCore 2 M) → pResidual 2 M ≤ N)
    (hgen : pResidual 2 M ⊔ T = ⊤)
    (hTY : T ≤ normalizer (Y : Set M))
    (hYE : Y ≤ E)
    (hZQ : Z ≤ centralizer (pCore 2 M : Set M))
    (hE : ¬ E ≤ pCore 2 M)
    (hQE : ⁅pCore 2 M,E⁆ ≤ E ⊓ pCore 2 M)
    (hlarge : ¬ ⁅pCore 2 M,pResidual 2 M⁆ ≤ Z)
    (hdisplacement : ∀ (N : Subgroup M) [N.Normal],
      N ≤ pCore 2 M → N ≤ centralizer (Y : Set M) → ⁅N,E⁆ ≤ Y) :
    ¬ ⁅normalClosure (Y : Set M),pResidual 2 M⁆ ≤ Z := by
  intro hcentral
  let A := normalClosure (Y : Set M)
  have hKY : pResidual 2 M ≤ normalizer ((Y ⊔ Z : Subgroup M) : Set M) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hKYZ : ⁅pResidual 2 M,Y ⊔ Z⁆ ≤ Z := by
      apply commutator_le.mpr
      intro k hk x hx
      obtain ⟨y,hy,z,hz,rfl⟩ := mem_sup_of_normal_right.mp hx
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hky : ⁅k,y⁆ ∈ Z := by
        rw [commutator_comm] at hcentral
        exact hcentral (commutator_mem_commutator hk (le_normalClosure hy))
      have hcz := (inferInstance : Z.Normal).conj_mem _
        (commutator_le_right (pResidual 2 M) Z (commutator_mem_commutator hk hz)) y
      simpa only [mul_assoc] using Z.mul_mem hky hcz
    exact hKYZ.trans le_sup_right
  have hTZ : T ≤ normalizer ((Y ⊔ Z : Subgroup M) : Set M) :=
    (le_inf hTY le_normalizer_of_normal).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : (Y ⊔ Z).Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hKY hTZ))
  have hA : A ≤ Y ⊔ Z := normalClosure_le_normal (show Y ≤ Y ⊔ Z from le_sup_left)
  let N := normalClosure ((E ⊓ pCore 2 M : Subgroup M) : Set M)
  have hNQ : N ≤ pCore 2 M := normalClosure_le_normal (show E ⊓ pCore 2 M ≤ _ from inf_le_right)
  have hIC : E ⊓ pCore 2 M ≤ centralizer (A : Set M) := by
    apply le_centralizer_iff.mp
    apply hA.trans
    apply sup_le
    · intro y hy x hx
      exact congrArg Subtype.val (mul_comm (⟨x,hx.1⟩ : E) ⟨y,hYE hy⟩)
    · exact hZQ.trans (centralizer_le (show E ⊓ pCore 2 M ≤ _ from inf_le_right))
  have hNC : N ≤ centralizer (A : Set M) := normalClosure_le_normal hIC
  have hNE : ⁅N,E⁆ ≤ A := (hdisplacement N hNQ
    (hNC.trans (centralizer_le le_normalClosure))).trans le_normalClosure
  have hNK : ⁅N,pResidual 2 M⁆ ≤ A := residual_detection hnormal N A E hE hNE
  have hKN : ⁅pCore 2 M,pResidual 2 M⁆ ≤ N :=
    residual_detection hnormal (pCore 2 M) N E hE (hQE.trans le_normalClosure)
  have hpN : IsPGroup 2 N := (pCore_isPGroup (p := 2) (G := M)).of_injective
    (inclusion hNQ) (inclusion_injective _)
  have hidN : ⁅⁅N,pResidual 2 M⁆,pResidual 2 M⁆ = ⁅N,pResidual 2 M⁆ :=
    commutator_isPPerfect_idempotent (pResidual 2 M) N
      (isPPerfect_pResidual 2) hpN le_normalizer_of_normal
  have hidQ : ⁅⁅pCore 2 M,pResidual 2 M⁆,pResidual 2 M⁆ =
      ⁅pCore 2 M,pResidual 2 M⁆ := commutator_isPPerfect_idempotent
        (pResidual 2 M) (pCore 2 M) (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal
  apply hlarge
  calc
    ⁅pCore 2 M,pResidual 2 M⁆ ≤ ⁅N,pResidual 2 M⁆ :=
      hidQ.symm.le.trans (commutator_mono hKN le_rfl)
    _ ≤ ⁅A,pResidual 2 M⁆ := hidN.symm.le.trans (commutator_mono hNK le_rfl)
    _ ≤ Z := hcentral

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
