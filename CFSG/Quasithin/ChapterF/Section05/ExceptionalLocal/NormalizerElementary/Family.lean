module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.Intersection
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.Transvections
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerFusion

/-!
# The four literal elementary subgroups of the exceptional Sylow

The source root-class counts distinguish the two mixed cores from A₁ and Q₂.
The graph involution separates A₁ from Q₂, while N_T(A₂)=C_T(t) separates
the mixed conjugates. The already proved family cardinal four therefore gives
the exact source labels. Conjugation preserves root-class counts and fixes Q₂,
so A₁ is also T-normal, and these are exactly the two normal members.

Source: Aschbacher–Smith F.5.4(4), printed p.301. The earlier-source
FusionFacts input is discharged by the independent source-fusion producer.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (t : G) (hf : FusionFacts c i z t)
local notation "T" => Source.sylowImage c i

omit [Finite G] in
include h in
/-- The literal plane core is normalized by the entire source Sylow. -/
theorem normalizer_T_normalizes_Q : T ≤ normalizer (Q c i true : Set G) := by
  rw [normalizer_Q_eq_plane c i z h]
  exact sylowImage_le_M c i true

include hf in
/-- The graph involution separates the point core from the ordinary plane core. -/
theorem normalizer_point_A_ne_Q : A c i false ≠ Q c i true := by
  intro he
  have hfg : Source.graphElement c i ∈ Q c i true := he ▸ graph_mem_A c i z t hf false
  have hfQ : zpowers (Source.graphElement c i) ≤ Q c i true := zpowers_le.mpr hfg
  let := source_Q_plane_elementary c i
  have hb : ⁅Q c i true,Q c i true⁆=⊥ := commutator_self_eq_bot_iff.mpr inferInstance
  have hz : zpowers t ≤ ⊥ := by
    rw [←hf.t_commutator]
    exact (commutator_mono le_rfl hfQ).trans_eq hb
  have ht1 : t=1 := hz (mem_zpowers t)
  have ho := hf.t_order
  rw [ht1,orderOf_one] at ho
  omega

include h hf in
/-- All maximal elementary subgroups of the literal source Sylow, with the
four source labels and the original conjugation convention. -/
theorem normalizer_elementary_list (y : G) (hy : y∈T) (hyt : y∉Tcentralizer c i t)
    (B : Subgroup G) :
    (B≤T ∧ IsElementaryAbelian 2 B ∧ Nat.card B=16) ↔
      B=A c i false ∨ B=A c i true ∨
      B=(A c i true).map (MulAut.conj y).toMonoidHom ∨ B=Q c i true := by
  classical
  have hAT (b : Bool) : A c i b≤T :=
    (A_le_TfImage c i z t hf b).trans ((TfImage_eq c i) ▸ inf_le_left)
  have hyT : (T).map (MulAut.conj y).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T).le_normalizer hy)
  have hAQ := normalizer_point_A_ne_Q c i z t hf
  have h12 : A c i false ≠ A c i true := by
    intro he
    have hh := hf.root_class_A_point
    rw [he,hf.root_class_A_plane] at hh
    omega
  have hQ2 : Q c i true ≠ A c i true := by
    intro he
    have hh := hf.root_class_Q_plane
    rw [he,hf.root_class_A_plane] at hh
    omega
  have hconjcard : Nat.card (classIntersection (rootElement c i z)
      ((A c i true).map (MulAut.conj y).toMonoidHom))=9 := by
    exact (classIntersection_card_conj (rootElement c i z) (A c i true) y).trans hf.root_class_A_plane
  have h1y : A c i false ≠ (A c i true).map (MulAut.conj y).toMonoidHom := by
    intro he
    have hh := hf.root_class_A_point
    rw [he,hconjcard] at hh
    omega
  have hQy : Q c i true ≠ (A c i true).map (MulAut.conj y).toMonoidHom := by
    intro he
    have hh := hf.root_class_Q_plane
    rw [he,hconjcard] at hh
    omega
  have h2y : A c i true ≠ (A c i true).map (MulAut.conj y).toMonoidHom := by
    intro he
    apply hyt
    rw [←normalizer_plane_A_in_T c i z h t hf]
    exact ⟨hy,mem_normalizer_iff_map_conj_eq.mpr he.symm⟩
  let Family := {B : Subgroup G // B≤T ∧ IsElementaryAbelian 2 B ∧ Nat.card B=16}
  let a : Family := ⟨A c i false,hAT false,hf.A_elementary false,hf.A_card false⟩
  let b : Family := ⟨A c i true,hAT true,hf.A_elementary true,hf.A_card true⟩
  let d : Family := ⟨(A c i true).map (MulAut.conj y).toMonoidHom,
    (map_mono (hAT true)).trans_eq hyT,by let := hf.A_elementary true;exact IsElementaryAbelian.map _,
    by rw [card_map_of_injective (MulAut.conj y).injective,hf.A_card]⟩
  let q : Family := ⟨Q c i true,source_Q_plane_le_sylowImage c i,
    source_Q_plane_elementary c i,source_Q_plane_card c i h.embedding_injective⟩
  let F : Fin 4 → Family := ![a,b,d,q]
  have hF : Function.Injective F := by
    intro u v huv
    have he := congrArg Subtype.val huv
    fin_cases u <;> fin_cases v <;> dsimp [F,a,b,d,q] at he ⊢ <;>
      first | rfl | exact (hAQ he).elim | exact (hAQ he.symm).elim |
        exact (h12 he).elim | exact (h12 he.symm).elim |
        exact (hQ2 he).elim | exact (hQ2 he.symm).elim |
        exact (h1y he).elim | exact (h1y he.symm).elim |
        exact (hQy he).elim | exact (hQy he.symm).elim |
        exact (h2y he).elim | exact (h2y he.symm).elim
  have hs : Function.Surjective F := ((Nat.bijective_iff_injective_and_card F).mpr
    ⟨hF,by rw [Nat.card_fin];exact (normalizer_elementary_family_card c i z h).symm⟩).surjective
  constructor
  · intro hB
    obtain ⟨n,he⟩ := hs ⟨B,hB⟩
    have hev := congrArg Subtype.val he
    fin_cases n <;> dsimp [F,a,b,d,q] at hev
    · exact Or.inl hev.symm
    · exact Or.inr (Or.inl hev.symm)
    · exact Or.inr (Or.inr (Or.inl hev.symm))
    · exact Or.inr (Or.inr (Or.inr hev.symm))
  · rintro (rfl | rfl | rfl | rfl)
    · exact a.property
    · exact b.property
    · exact d.property
    · exact q.property

include h hf in
/-- The point elementary core is normal in the original Sylow. -/
theorem normalizer_T_normalizes_A_point (y : G) (hy : y∈T)
    (hyt : y∉Tcentralizer c i t) : T ≤ normalizer (A c i false : Set G) := by
  classical
  have hAT : A c i false≤T :=
    (A_le_TfImage c i z t hf false).trans ((TfImage_eq c i) ▸ inf_le_left)
  intro x hx
  have hxT : (T).map (MulAut.conj x).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T).le_normalizer hx)
  let := hf.A_elementary false
  have he : IsElementaryAbelian 2 ((A c i false).conjBy x) := IsElementaryAbelian.map _
  have hc : Nat.card ((A c i false).conjBy x)=16 := by
    rw [conjBy,card_map_of_injective (MulAut.conj x).injective,hf.A_card]
  have hclass := classIntersection_card_conj (rootElement c i z) (A c i false) x
  rw [hf.root_class_A_point] at hclass
  have hlist := (normalizer_elementary_list c i z h t hf y hy hyt
    ((A c i false).conjBy x)).mp ⟨(map_mono hAT).trans_eq hxT,he,hc⟩
  rcases hlist with heq | heq | heq | heq
  · exact mem_normalizer_iff_map_conj_eq.mpr heq
  · rw [heq,hf.root_class_A_plane] at hclass
    omega
  · change (A c i false).conjBy x=(A c i true).conjBy y at heq
    rw [heq,classIntersection_card_conj,hf.root_class_A_plane] at hclass
    omega
  · have hQfix : (Q c i true).conjBy x⁻¹=Q c i true :=
      mem_normalizer_iff_map_conj_eq.mp
        (normalizer_T_normalizes_Q c i z h ((T).inv_mem hx))
    have hh := congrArg (fun B : Subgroup G => B.conjBy x⁻¹) heq
    rw [conjBy_inv,hQfix] at hh
    exact (normalizer_point_A_ne_Q c i z t hf hh).elim

include h hf in
/-- Only A₁ and Q₂ among the four elementary sixteen-groups are T-normal. -/
theorem normalizer_elementary_normal_cases (y : G) (hy : y∈T)
    (hyt : y∉Tcentralizer c i t) (B : Subgroup G) (hBT : B≤T)
    (he : IsElementaryAbelian 2 B) (hc : Nat.card B=16)
    (hN : T≤normalizer (B : Set G)) : B=A c i false ∨ B=Q c i true := by
  rcases (normalizer_elementary_list c i z h t hf y hy hyt B).mp ⟨hBT,he,hc⟩
    with hB | hB | hB | hB
  · exact Or.inl hB
  · apply (hyt ?_).elim
    rw [←normalizer_plane_A_in_T c i z h t hf]
    exact ⟨hy,hB ▸ hN hy⟩
  · have hfix : B.conjBy y⁻¹=B :=
      mem_normalizer_iff_map_conj_eq.mp (hN ((T).inv_mem hy))
    change B=(A c i true).conjBy y at hB
    have hBA : B=A c i true := by
      rw [hB,conjBy_inv] at hfix
      exact hB.trans hfix.symm
    apply (hyt ?_).elim
    rw [←normalizer_plane_A_in_T c i z h t hf]
    exact ⟨hy,hBA ▸ hN hy⟩
  · exact Or.inr hB

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
