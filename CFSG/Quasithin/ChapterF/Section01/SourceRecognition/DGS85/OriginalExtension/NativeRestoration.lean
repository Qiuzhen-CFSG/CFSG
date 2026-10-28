module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Completion
/-!
# Native compatible lifts in original DGS restoration

A compatible automorphism of a reduced model that extends to its concrete
completion preserves the literal kernel of the universal completion map.
Transporting through a marked amalgam isomorphism keeps both endpoint maps
and the full middle map. This allows the proved native lift theorems to
supply the descent premise in DGS (15.2), pp.226–228, without repeating the
Cartan argument for those models. Sylow conjugacy supplies the needed
endpoint normalizers. If every two-power automorphism of the model is inner,
faithfulness forces the original source S to equal its reduced subgroup.
Model recognition remains a separate input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.NativeRestoration
universe u v
variable {L B R : Type u} {L' B' R' : Type v}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']
  {X K : Type*} [Group X] [Group K]
  {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
  (a : K →* Iso α α) (e : Iso α β) (c : FaithfulCompletion β (G := X))

/-- Native endpoint lifts preserve the actual universal kernel after marked
transport. Endomorphisms suffice; no action law or kernel premise is assumed. -/
theorem preserves_of_native_lifts
    (hlift : ∀ b : Iso β β, ∃ f : X →* X,
      (∀ x, f (c.left x) = c.left (b.left x)) ∧
      (∀ x, f (c.right x) = c.right (b.right x))) :
    CompletionAction.PreservesCompletionKernel a (c.comapIso e) := by
  intro k
  let b := automorphismConjEquiv e (a k)
  obtain ⟨f,hl,hr⟩ := hlift b
  have he : Universal.lift α ((c.comapIso e).comapIso (a k)) =
      f.comp (Universal.lift α (c.comapIso e)) := by
    apply Monoid.PushoutI.hom_ext_nonempty
    intro i
    cases i <;> ext x
    · change L at x
      change Universal.lift α ((c.comapIso e).comapIso (a k)) (Universal.left α x) =
        f (Universal.lift α (c.comapIso e) (Universal.left α x))
      rw [Universal.lift_left, Universal.lift_left]
      change c.left (e.left ((a k).left x)) = f (c.left (e.left x))
      rw [hl]
      congr 1
      exact congrArg e.left (congrArg (a k).left (e.left.symm_apply_apply x)).symm
    · change R at x
      change Universal.lift α ((c.comapIso e).comapIso (a k)) (Universal.right α x) =
        f (Universal.lift α (c.comapIso e) (Universal.right α x))
      rw [Universal.lift_right, Universal.lift_right]
      change c.right (e.right ((a k).right x)) = f (c.right (e.right x))
      rw [hr]
      congr 1
      exact congrArg e.right (congrArg (a k).right (e.right.symm_apply_apply x)).symm
  intro x hx
  change Universal.lift α ((c.comapIso e).comapIso (a k)) x = 1
  rw [he]
  change f (Universal.lift α (c.comapIso e) x) = 1
  rw [show Universal.lift α (c.comapIso e) x = 1 from hx, map_one]
/-- Sylow conjugacy makes every overgroup containing the ambient Sylow
normalizer self-normalizing. -/
theorem self_normalizing_of_sylow {Y : Type*} [Group Y] [Finite Y]
    (S : Sylow 2 Y) (P : Subgroup Y) (hSP : (S : Subgroup Y) ≤ P)
    (hNP : normalizer (S : Set Y) ≤ P) : normalizer (P : Set Y) = P := by
  apply le_antisymm _ P.le_normalizer
  intro g hg
  have hSg : (g • S : Sylow 2 Y) ≤ P := by
    change (S : Subgroup Y).map (MulAut.conj g).toMonoidHom ≤ P
    rw [← mem_normalizer_iff_map_conj_eq.mp hg]
    exact map_mono hSP
  obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P ((g • S).subtype hSg) (S.subtype hSP)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hp
  have hn : (p : Y)*g ∈ normalizer (S : Set Y) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hp)
  simpa only [inv_mul_cancel_left] using P.mul_mem (P.inv_mem p.property) (hNP hn)


section Original
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 P S)
  (d : FaithfulCompletion (reducedAmalgam P S) (G := X))
  (hk : PreservesCompletionKernel h d)
  (ho : d.left.range ⊓ d.right.range = d.middle.range)
  (hN : ∀ i, normalizer ((completionEndpoint d i).range : Set X) =
    (completionEndpoint d i).range)

include h d hk ho hN in
/-- If the concrete completion has no outer two-elements, the original
source S cannot enlarge the reduced Sylow. This uses the faithful full-Borel
action, not an assumed original bound or an ambient Sylow identification. -/
theorem sylow_eq_reduced_of_twoPower_inner
    (hinner : ∀ (a : MulAut X) (k : ℕ), a^(2^k)=1 → a ∈ MulAut.innerSubgroup X) :
    S = SuzukiContainment.reducedSylow P S := by
  have hSB : S ≤ commonBorel P (SuzukiContainment.reducedSylow P S) := by
    intro x hx
    let b : commonBorel P S := ⟨x, (show S ≤ commonBorel P S from le_sup_right) hx⟩
    obtain ⟨k,hkpow⟩ := h.S_isP ⟨x,hx⟩
    have hb : b^(2^k)=1 := Subtype.ext (congrArg (fun z : S => (z : G)) hkpow)
    have ha : completionAction h d hk b ∈ MulAut.innerSubgroup X :=
      hinner _ k (by rw [← map_pow, hb, map_one])
    exact (completionAction_mem_inner_iff h d hk ho hN b).mp ha
  exact le_antisymm (by
    rw [← reduced_borel_inf_sylow h]
    exact le_inf hSB le_rfl) (SuzukiContainment.reducedSylow_le h)

/-- Identity on ambient elements, with commuting squares checked before
specializing the subgroups to the original and reduced source formulas. -/
@[expose] def subgroupCongrIso {Y : Type*} [Group Y]
    {A B C A' B' C' : Subgroup Y}
    (hA : B ≤ A) (hC : B ≤ C) (hA' : B' ≤ A') (hC' : B' ≤ C')
    (eA : A = A') (eB : B = B') (eC : C = C') :
    Iso (ofSubgroups A B C hA hC) (ofSubgroups A' B' C' hA' hC') where
  left := MulEquiv.subgroupCongr eA
  middle := MulEquiv.subgroupCongr eB
  right := MulEquiv.subgroupCongr eC
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- The abstract subgroup transport preserves a given marking on each
included subgroup. This avoids unfolding the source subgroup formulas. -/
theorem subgroupCongrIso_trans_reduced {Y : Type*} [Group Y]
    {A B C A' B' C' : Subgroup Y}
    (hA : B ≤ A) (hC : B ≤ C) (hA' : B' ≤ A') (hC' : B' ≤ C')
    (eA : A = A') (eB : B = B') (eC : C = C')
    {L₀ B₀ R₀ : Type*} [Group L₀] [Group B₀] [Group R₀]
    {γ : RankTwoAmalgam L₀ B₀ R₀}
    (e : Iso (ofSubgroups A' B' C' hA' hC') γ)
    (jA : A' ≤ A) (jB : B' ≤ B) (jC : C' ≤ C) :
    (∀ x : A', ((subgroupCongrIso hA hC hA' hC' eA eB eC).trans e).left
      (inclusion jA x) = e.left x) ∧
    (∀ x : B', ((subgroupCongrIso hA hC hA' hC' eA eB eC).trans e).middle
      (inclusion jB x) = e.middle x) ∧
    (∀ x : C', ((subgroupCongrIso hA hC hA' hC' eA eB eC).trans e).right
      (inclusion jC x) = e.right x) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- When the original S has been proved equal to its reduced subgroup, the
original and reduced inclusion diagrams agree on every ambient element. -/
@[expose] def originalIsoReduced (hS : S = SuzukiContainment.reducedSylow P S) :
    Iso (originalAmalgam P S) (reducedAmalgam P S) :=
  subgroupCongrIso _ _ _ _ (congrArg (fun U => parabolic P U 0) hS)
    (congrArg (commonBorel P) hS) (congrArg (fun U => parabolic P U 1) hS)

end Original

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 P S)
  {L' B' R' : Type*} [Group L'] [Group B'] [Group R']
  {β : RankTwoAmalgam L' B' R'}

/-- Composition with a reduced marking preserves all three literal inclusions. -/
theorem originalIsoReduced_trans_reduced (hS : S = SuzukiContainment.reducedSylow P S)
    (e : Iso (reducedAmalgam P S) β) :
    (∀ x : parabolic P (SuzukiContainment.reducedSylow P S) 0,
      ((originalIsoReduced hS).trans e).left
        (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) = e.left x) ∧
    (∀ x : commonBorel P (SuzukiContainment.reducedSylow P S),
      ((originalIsoReduced hS).trans e).middle
        (inclusion (SuzukiContainment.reduced_commonBorel_le h) x) = e.middle x) ∧
    (∀ x : parabolic P (SuzukiContainment.reducedSylow P S) 1,
      ((originalIsoReduced hS).trans e).right
        (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) = e.right x) :=
  subgroupCongrIso_trans_reduced _ _ _ _ _ _ _ e
    (SuzukiContainment.reduced_parabolic_le h 0)
    (SuzukiContainment.reduced_commonBorel_le h)
    (SuzukiContainment.reduced_parabolic_le h 1)


end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.NativeRestoration
