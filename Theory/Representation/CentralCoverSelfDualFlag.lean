module
public import Theory.Representation.FirstCohomologyDuality.SimpleCover
public import Theory.Representation.SubrepresentationRadical
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Order.Fin.Basic

/-!
# Central covers and self-dual invariant flags

A simple fixed-point-free module has no nonzero map into a nontrivial perfect
central cover with simple head. Orthogonal complements from an invariant
nondegenerate symmetric pairing reverse the invariant-subspace lattice.
A complete strictly decreasing finite flag is its literal iterated radical
flag, since each predecessor is the greatest proper invariant subspace.

The final rank argument isolates the six possible subspaces in a
fourteen-dimensional self-dual module with a four-dimensional essential socle
and the two five-dimensional covering sections. Existence of the middle
five-space is supplied separately by the actual covering map.

Source application: Aschbacher--Smith, G.5.3(2)--(5), printed pp.344--345.
-/

@[expose] public section
namespace Representation.BinaryCoverSocle
open Representation.OneCohomology

/-- An invariant nondegenerate pairing identifies an action with its contragredient. -/
noncomputable def selfDualOfPairing
    {k H V : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k H V)
    (B : V →ₗ[k] Module.Dual k V) (hB : Function.Injective B)
    (hinv : ∀ g v w, B (ρ g v) w = B v (ρ g⁻¹ w)) : ρ.Equiv ρ.dual :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective B ⟨hB,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hB⟩)
    (fun g => LinearMap.ext (fun v => LinearMap.ext (fun w => hinv g v w)))


variable {k G V W X : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G W} {τ : Representation k G X}

/-- The image of a simple module in a nontrivial perfect central cover is fixed. -/
theorem simple_map_fixed [IsIrreducible ρ] [IsIrreducible τ]
    (p : σ.IntertwiningMap τ) (hp : OneCohomology.IsCover p)
    (hk : p.toLinearMap.ker ≠ ⊥) (f : ρ.IntertwiningMap σ) (v : V) (g : G) :
    σ g (f v) = f v := by
  have hz : p.comp f = 0 := by
    rcases IsIrreducible.bijective_or_eq_zero (p.comp f) with h | h
    · have hr : f.range.toSubmodule.map p.toLinearMap = ⊤ := by
        apply top_unique
        intro x _
        obtain ⟨v, rfl⟩ := h.2 x
        exact ⟨f v, ⟨v, rfl⟩, rfl⟩
      have hf : Function.Surjective f := LinearMap.range_eq_top.mp
        (OneCohomology.invariant_eq_top_of_cover_image_eq_top p hp f.range.toSubmodule
          (fun g _ hv => f.range.apply_mem_toSubmodule g hv) hr)
      have hi : Function.Injective p := by
        intro x y hxy
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hf y
        exact congrArg f (h.1 hxy)
      exact False.elim (hk (LinearMap.ker_eq_bot.mpr hi))
    · exact h
  apply hp.2.1
  exact congrArg (fun q : ρ.IntertwiningMap τ => q v) hz

/-- An injective map from a simple module into a fixed-point-free ambient module
cannot have a nonzero composite with a nontrivial perfect central cover. -/
theorem simple_map_to_cover_eq_zero [IsIrreducible ρ] [IsIrreducible τ]
    (p : σ.IntertwiningMap τ) (hp : OneCohomology.IsCover p)
    (hk : p.toLinearMap.ker ≠ ⊥) (f : ρ.IntertwiningMap σ)
    (hρ : fixed ρ = ⊥) : f = 0 := by
  rcases IsIrreducible.injective_or_eq_zero f with hf | hf
  · apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixed ρ := by
      intro g
      apply hf
      rw [f.isIntertwining]
      exact simple_map_fixed p hp hk f v g
    rw [hρ] at hv
    simp only [show v = 0 from hv, map_zero]
  · exact hf

/-- Orthogonal complement for an invariant nondegenerate symmetric pairing. -/
def perp (e : ρ.Equiv ρ.dual) (S : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualAnnihilator.comap e.toLinearEquiv.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change e v ∈ S.toSubmodule.dualAnnihilator at hv
    change e (ρ g v) ∈ S.toSubmodule.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator] at hv ⊢
    intro w hw
    exact (congrArg (fun l : Module.Dual k V => l w)
      (IntertwiningMap.isIntertwining ρ ρ.dual e.toIntertwiningMap g v)).trans
        (hv (ρ g⁻¹ w) (S.apply_mem_toSubmodule g⁻¹ hw))

theorem mem_perp (e : ρ.Equiv ρ.dual) (S : Subrepresentation ρ) (v : V) :
    v ∈ perp e S ↔ ∀ w ∈ S, e v w = 0 := by
  exact Submodule.mem_dualAnnihilator _

theorem perp_antitone (e : ρ.Equiv ρ.dual) : Antitone (perp e) := by
  intro S T h v hv
  rw [mem_perp] at hv ⊢
  intro w hw
  exact hv w (h hw)

theorem perp_finrank [FiniteDimensional k V] (e : ρ.Equiv ρ.dual)
    (S : Subrepresentation ρ) :
    Module.finrank k S.toSubmodule + Module.finrank k (perp e S).toSubmodule =
      Module.finrank k V := by
  rw [show Module.finrank k (perp e S).toSubmodule =
    Module.finrank k S.toSubmodule.dualAnnihilator from
    (e.toLinearEquiv.ofSubmodule' S.toSubmodule.dualAnnihilator).finrank_eq]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq _

theorem perp_perp [FiniteDimensional k V] (e : ρ.Equiv ρ.dual)
    (he : ∀ v w, e v w = e w v) (S : Subrepresentation ρ) :
    perp e (perp e S) = S := by
  apply Subrepresentation.toSubmodule_injective
  apply (Submodule.eq_of_le_of_finrank_eq (S₁ := S.toSubmodule) ?_ ?_).symm
  · intro v hv
    change v ∈ perp e (perp e S)
    rw [mem_perp]
    intro w hw
    rw [he]
    exact (mem_perp e S w).mp hw v hv
  · have h₁ := perp_finrank e S
    have h₂ := perp_finrank e (perp e S)
    omega

end Representation.BinaryCoverSocle

namespace Representation.BinaryCoverSocle
open Representation.OneCohomology
variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] {ρ : Representation k G V}

theorem finrank_bottom :
    Module.finrank k (⊥ : Subrepresentation ρ).toSubmodule = 0 :=
  finrank_bot _ _

theorem finrank_whole :
    Module.finrank k (⊤ : Subrepresentation ρ).toSubmodule = Module.finrank k V :=
  finrank_top _ _

/-- Pull an ambient invariant subspace back to a restricted representation. -/
def restrict (A B : Subrepresentation ρ) : Subrepresentation B.toRepresentation where
  toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := A.apply_mem_toSubmodule g hv

/-- Embed an invariant subspace of a restricted representation in the ambient one. -/
def embed (B : Subrepresentation ρ) (A : Subrepresentation B.toRepresentation) :
    Subrepresentation ρ where
  toSubmodule := A.toSubmodule.map B.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨B.toRepresentation g v, A.apply_mem_toSubmodule g hv, rfl⟩

theorem embed_restrict (A B : Subrepresentation ρ) (h : A ≤ B) :
    embed B (restrict A B) = A := by
  apply Subrepresentation.toSubmodule_injective
  exact (Submodule.map_comap_subtype _ _).trans (inf_eq_right.mpr h)

theorem restrict_embed (B : Subrepresentation ρ) (A : Subrepresentation B.toRepresentation) :
    restrict (embed B A) B = A := by
  apply Subrepresentation.toSubmodule_injective
  exact (Submodule.comap_map_eq _ _).trans (by simp)

theorem embed_le (B : Subrepresentation ρ) (A : Subrepresentation B.toRepresentation) :
    embed B A ≤ B := by rintro _ ⟨v, _, rfl⟩; exact v.property

theorem embed_mono (B : Subrepresentation ρ) : Monotone (embed B) := by
  intro A C h x hx
  rcases hx with ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem embed_le_iff (B : Subrepresentation ρ) (A C : Subrepresentation B.toRepresentation) :
    embed B A ≤ embed B C ↔ A ≤ C := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, he⟩ := h (show v.val ∈ embed B A from ⟨v, hv, rfl⟩)
    exact (Subtype.ext he : w = v) ▸ hw
  · intro h
    exact embed_mono B h

theorem embed_top (B : Subrepresentation ρ) : embed B ⊤ = B := by
  apply le_antisymm (embed_le B ⊤)
  intro v hv
  exact ⟨⟨v, hv⟩, Submodule.mem_top, rfl⟩

theorem embed_bot (B : Subrepresentation ρ) : embed B ⊥ = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.map_bot _

end Representation.BinaryCoverSocle

namespace Representation.BinaryCoverSocle
variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] {ρ : Representation k G V}

theorem embed_finrank [FiniteDimensional k V] (B : Subrepresentation ρ)
    (A : Subrepresentation B.toRepresentation) :
    Module.finrank k (embed B A).toSubmodule = Module.finrank k A.toSubmodule :=
  (Submodule.equivMapOfInjective B.toSubmodule.subtype
    B.toSubmodule.subtype_injective A.toSubmodule).finrank_eq.symm

/-- A greatest proper invariant subspace is the radical of the restricted action,
embedded by the literal subtype map. -/
theorem within_eq_of_greatest_proper (S R : Subrepresentation ρ) (hRS : R < S)
    (hmax : ∀ T : Subrepresentation ρ, T < S → T ≤ R) :
    ModuleRadical.within S = R := by
  classical
  let r := restrict R S
  have her : embed S r = R := embed_restrict R S hRS.le
  have hrne : r ≠ ⊤ := by
    intro he
    have hh := congrArg (embed S) he
    rw [her, embed_top] at hh
    exact hRS.ne hh
  have proper (T : Subrepresentation S.toRepresentation) (ht : T ≠ ⊤) : T ≤ r := by
    apply (embed_le_iff S T r).mp
    rw [her]
    apply hmax
    refine lt_of_le_of_ne (embed_le S T) ?_
    intro he
    apply ht
    apply le_antisymm le_top
    apply (embed_le_iff S ⊤ T).mp
    rw [embed_top, he]
  have hr : IsCoatom r := ⟨hrne, fun T ht => by
    by_contra hn
    exact (not_le_of_gt ht) (proper T hn)⟩
  have unique (T : Subrepresentation S.toRepresentation) (ht : IsCoatom T) : T = r := by
    rcases eq_or_lt_of_le (proper T ht.1) with he | hl
    · exact he
    · exact False.elim (hrne (ht.2 r hl))
  have hrad : ModuleRadical.radical S.toRepresentation = r := by
    change sInf {N : Subrepresentation S.toRepresentation | IsCoatom N} = r
    apply le_antisymm
    · exact sInf_le hr
    apply le_sInf
    intro T ht
    exact (unique T ht).symm ▸ le_rfl
  change embed S (ModuleRadical.radical S.toRepresentation) = R
  rw [hrad, her]

end Representation.BinaryCoverSocle

namespace Representation.BinaryCoverSocle
variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- A complete strictly decreasing invariant flag is the literal radical flag. -/
theorem within_flag (F : Fin 6 → Subrepresentation ρ) (hF : StrictAnti F)
    (hc : ∀ S : Subrepresentation ρ, S ≤ F 0 → ∃ j, S = F j) (i : Fin 5) :
    ModuleRadical.within (F i.castSucc) = F i.succ := by
  apply within_eq_of_greatest_proper _ _ (hF (by simp))
  intro S hS
  obtain ⟨j, rfl⟩ := hc S (hS.le.trans (hF.antitone (Fin.zero_le _)))
  apply hF.antitone
  by_contra hn
  have hji : j ≤ i.castSucc := by
    change j.val ≤ i.val
    change ¬ i.val + 1 ≤ j.val at hn
    omega
  exact (not_le_of_gt hS) (hF.antitone hji)

theorem flag_covBy (F : Fin 6 → Subrepresentation ρ) (hF : StrictAnti F)
    (hc : ∀ S : Subrepresentation ρ, S ≤ F 0 → ∃ j, S = F j) (i : Fin 5) :
    CovBy (F i.succ) (F i.castSucc) := by
  refine ⟨hF (by simp), ?_⟩
  intro S hlow hhigh
  obtain ⟨j, rfl⟩ := hc S (hhigh.le.trans (hF.antitone (Fin.zero_le _)))
  have hi : i.succ ≤ j := by
    by_contra hn
    have hji : j ≤ i.castSucc := by
      change j.val ≤ i.val
      change ¬ i.val + 1 ≤ j.val at hn
      omega
    exact (not_le_of_gt hhigh) (hF.antitone hji)
  exact (not_le_of_gt hlow) (hF.antitone hi)

end Representation.BinaryCoverSocle



namespace Representation.SelfDualFiveFlag

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- The two three-element section lattices and a unique socle force the whole
fourteen-dimensional self-dual lattice to have at most six elements. -/
theorem cases_of_rank_data (r : L → ℕ) (hr : StrictMono r)
    (hbot : r ⊥ = 0) (htop : r ⊤ = 14)
    (hsum : ∀ S T, r (S ⊔ T) + r (S ⊓ T) = r S + r T)
    (p : L → L) (hp : Antitone p) (hpp : ∀ S, p (p S) = S)
    (hrp : ∀ S, r S + r (p S) = 14)
    (C D : L) (hC : r C = 4) (hD : r D = 9) (hCD : C ≤ D)
    (hsoc : ∀ S, S ≠ ⊥ → C ≤ S)
    (hmid : ∀ S, C ≤ S → S ≤ D → r S = 4 ∨ r S = 5 ∨ r S = 9)
    (hupper : ∀ S, D ≤ S → r S = 9 ∨ r S = 10 ∨ r S = 14)
    (S : L) : S = ⊥ ∨ S = C ∨ S = p D ∨ S = D ∨ S = p C ∨ S = ⊤ := by
  have eq_of_le {A B : L} (h : A ≤ B) (he : r A = r B) : A = B :=
    le_antisymm h (by by_contra hn; have := hr (lt_of_le_not_ge h hn); omega)
  have eq_bot {T : L} (h : r T = 0) : T = ⊥ := (eq_of_le bot_le (hbot.trans h.symm)).symm
  have eq_top {T : L} (h : r T = 14) : T = ⊤ := eq_of_le le_top (h.trans htop.symm)
  have hcperp : r (p C) = 10 := by have := hrp C; omega
  have proper_le (T : L) (hT : T ≠ ⊤) : T ≤ p C := by
    have hn : p T ≠ ⊥ := by
      intro h
      have := hrp T
      rw [h, hbot] at this
      exact hT (eq_top (by omega))
    simpa only [hpp] using hp (hsoc (p T) hn)
  have hdtop : D ≠ ⊤ := by intro he; rw [he, htop] at hD; omega
  have ranks_not_le (T : L) (hn : ¬ T ≤ D) (ht : T ≠ ⊤) :
      r T = 5 ∨ r T = 6 ∨ r T = 10 := by
    have hT : T ≠ ⊥ := fun he => hn (he ▸ bot_le)
    have hci : C ≤ T ⊓ D := le_inf (hsoc T hT) hCD
    have hi := hmid (T ⊓ D) hci inf_le_right
    have hs : r (T ⊔ D) = 10 := by
      have hu := hupper (T ⊔ D) le_sup_right
      have hb : r (T ⊔ D) ≤ 10 := hcperp ▸ hr.monotone
        (sup_le (proper_le T ht) (proper_le D hdtop))
      have he : r (T ⊔ D) ≠ 9 := by
        intro he
        have hh : T ⊔ D = D := (eq_of_le le_sup_right (hD.trans he.symm)).symm
        exact hn (hh ▸ le_sup_left)
      omega
    have := hsum T D
    omega
  have ranks (T : L) :
      r T = 0 ∨ r T = 4 ∨ r T = 5 ∨ r T = 6 ∨ r T = 9 ∨ r T = 10 ∨ r T = 14 := by
    by_cases hb : T = ⊥
    · exact Or.inl (hb ▸ hbot)
    by_cases ht : T = ⊤
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ht ▸ htop))))))
    by_cases hd : T ≤ D
    · have := hmid T (hsoc T hb) hd
      omega
    · have := ranks_not_le T hd ht
      omega
  have rank4 (T : L) (h : r T = 4) : T = C := by
    have hn : T ≠ ⊥ := by intro he; rw [he, hbot] at h; omega
    exact (eq_of_le (hsoc T hn) (hC.trans h.symm)).symm
  have rank9 (T : L) (h : r T = 9) : T = D := by
    have ht : T ≠ ⊤ := by intro he; rw [he, htop] at h; omega
    have hd : T ≤ D := by
      by_contra hn
      have := ranks_not_le T hn ht
      omega
    exact eq_of_le hd (h.trans hD.symm)
  have hs := ranks S
  have hps := ranks (p S)
  have hpdim := hrp S
  rcases hs with h | h | h | h | h | h | h
  · exact Or.inl (eq_bot h)
  · exact Or.inr (Or.inl (rank4 S h))
  · have he : p S = D := rank9 (p S) (by omega)
    have he' : S = p D := by simpa only [hpp] using congrArg p he
    exact Or.inr (Or.inr (Or.inl he'))
  · omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl (rank9 S h))))
  · have he : p S = C := rank4 (p S) (by omega)
    have he' : S = p C := by simpa only [hpp] using congrArg p he
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_top h)))))

end Representation.SelfDualFiveFlag
