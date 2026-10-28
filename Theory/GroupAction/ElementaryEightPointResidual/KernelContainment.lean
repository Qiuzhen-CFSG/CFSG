module
public import Theory.GroupAction.ElementaryEightPointResidual.PointCentralization
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PCoreImage

/-!
# Full covering kernels at a Sylow subgroup of index two

Let a normal subgroup D cover GL₃(2) with kernel O₂(D). Suppose R has
index two in a Sylow P and R intersect D has image contained in an A₄.
Then O₂(D) lies in R, and R together with P intersect D generates P.
Indeed the latter intersection maps onto a group of order eight. If the
kernel escaped R, adjoining it would fill P without enlarging this image,
contradicting its containment in a group of order twelve.

This keeps the full kernel and the literal component intersection in
Aschbacher–Smith 14.7.6, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupAction.ElementaryEightPointResidual
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem intermediate_of_index_two (R P A : Subgroup G)
    (hRA : R ≤ A) (hAP : A ≤ P) (hi : R.relIndex P = 2) : A = R ∨ A = P := by
  have hm := relIndex_mul_relIndex R A P hRA hAP
  rw [hi] at hm
  rcases (Nat.dvd_prime Nat.prime_two).mp (show R.relIndex A ∣ 2 from ⟨_,hm.symm⟩) with he | he
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp he) hRA)
  · rw [he] at hm
    exact Or.inr (le_antisymm hAP (relIndex_eq_one.mp (by omega : A.relIndex P = 1)))

/-- The full kernel of a normal cover lies in an index-two Sylow subgroup
whose component intersection has only an A₄ point image. The component
intersection with the larger Sylow supplies the missing coset as well. -/
theorem normal_cover_kernel_le_of_index_two
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (f : G →* MulAut E)
    (D : Subgroup G) [D.Normal] (hD : D.map f = ⊤)
    (hk : (f.comp D.subtype).ker = pCore 2 D)
    (P : Sylow 2 G) (R : Subgroup G) (hRP : R ≤ P)
    (hi : R.relIndex (P : Subgroup G) = 2)
    (B : Subgroup (MulAut E)) (hB : Nat.card B = 12)
    (himage : (R ⊓ D).map f ≤ B) :
    D.pCoreIn 2 ≤ R ∧ R ⊔ ((P : Subgroup G) ⊓ D) = (P : Subgroup G) := by
  let Q := D.pCoreIn 2
  have hQker : Q ≤ f.ker := by
    rintro x ⟨d,hd,rfl⟩
    exact (hk.symm ▸ hd : d ∈ (f.comp D.subtype).ker)
  let : Q.Normal := inferInstanceAs ((pCore 2 D).map D.subtype).Normal
  have hQP : Q ≤ P := (isPGroup_pCoreIn 2 D).le_sylow_of_normal P
  have hf : Function.Surjective (f.comp D.subtype) := by
    intro e
    obtain ⟨d,hd,hde⟩ := hD.ge (mem_top e)
    exact ⟨⟨d,hd⟩,hde⟩
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal D
  have h8 : Nat.card (((P : Subgroup G) ⊓ D).map f) = 8 := by
    have he : ((P : Subgroup G) ⊓ D).map f = (S.mapSurjective hf : Subgroup (MulAut E)) := by
      rw [Sylow.coe_mapSurjective,←map_map,hS,subgroupOf_map_subtype]
    rw [he,Sylow.card_eq_multiplicity,card_mulAut_of_elementary_eight E hE]
    decide +kernel
  have hnot : ¬ (P : Subgroup G) ⊓ D ≤ R := by
    intro hle
    have he : (P : Subgroup G) ⊓ D = R ⊓ D := le_antisymm
      (le_inf hle inf_le_right) (inf_le_inf_right _ hRP)
    have hd := card_dvd_of_le himage
    rw [←he,h8,hB] at hd
    norm_num at hd
  have hgen : R ⊔ ((P : Subgroup G) ⊓ D) = (P : Subgroup G) := by
    rcases intermediate_of_index_two R (P : Subgroup G) _ le_sup_left
        (sup_le hRP inf_le_left) hi with he | he
    · exact (hnot (le_sup_right.trans he.le)).elim
    · exact he
  have hcore : Q ≤ R := by
    rcases intermediate_of_index_two R (P : Subgroup G) (R ⊔ Q) le_sup_left
        (sup_le hRP hQP) hi with he | he
    · exact le_sup_right.trans he.le
    · have hle : ((P : Subgroup G) ⊓ D).map f ≤ (R ⊓ D).map f := by
        rintro x ⟨p,hp,rfl⟩
        obtain ⟨r,hr,q,hq,hrq⟩ := mem_sup_of_normal_right.mp (he.symm ▸ hp.1)
        have hqD : q ∈ D := pCoreIn_le 2 D hq
        have hrD : r ∈ D := by
          have hh := D.mul_mem hp.2 (D.inv_mem hqD)
          rwa [←hrq,mul_inv_cancel_right] at hh
        refine ⟨r,⟨hr,hrD⟩,?_⟩
        rw [←hrq,map_mul,show f q = 1 from hQker hq,mul_one]
      have hd := card_dvd_of_le (hle.trans himage)
      rw [h8,hB] at hd
      norm_num at hd
  exact ⟨hcore,hgen⟩

end Theory.GroupAction.ElementaryEightPointResidual
