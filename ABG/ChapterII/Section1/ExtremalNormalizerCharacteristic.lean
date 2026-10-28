module

public import ABG.ChapterII.Section1.ExtremalNormalizerCore
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.BGsection6.Defs
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Centric normalizer actions in solvable local groups

For an extremal centric p-subgroup X, suppose its normalizer is solvable
and has trivial p′-core. Then the full ambient centralizer of X lies in X.
Consequently the kernel of the actual normalizer action is a p-group.
If the center of X also has p-group automorphisms, the induced action on
X/Z(X) has p-group kernel. Any subgroup acting trivially on this quotient
therefore lies in the normalizer p-core.

The action kernel C is normal in N(X). Its p-core is normal in N(X), so
extremality places it in the chosen Sylow. Centricity puts it inside X,
where it is centralized by C. The normal subgroup C has trivial p′-core;
Fitting self-centralization therefore makes C a p-group. A second use of
extremality and centricity gives the claimed full-centralizer containment.

This is the characteristic-p reduction for the centric fusion argument of
ABG Chapter II §1, applied to Stellmacher (8.6)(a).
-/

namespace ABG

open BenderSuzuki.External

/-- With a solvable normalizer and trivial local p′-core, extremal
centricity implies containment of the full ambient centralizer. -/
public theorem centralizer_le_of_extremal_centric
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (X : Subgroup G) (hX : HuppertExtremal P X)
    (hc : subgroupCentralizerIn (P : Subgroup G) X ≤ X)
    (hsolv : Group.IsSolvable (Subgroup.normalizer (X : Set G)))
    (hodd : pPrimeCore p (Subgroup.normalizer (X : Set G)) = ⊥) :
    Subgroup.centralizer (X : Set G) ≤ X := by
  let N := Subgroup.normalizer (X : Set G)
  let φ : N →* MulAut X := X.normalizerMonoidHom
  let C := φ.ker
  let : Group.IsSolvable N := hsolv
  have hoddC : pPrimeCore p C = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    exact le_bot_iff.mp ((pPrimeCore_map_subtype_le_pPrimeCore_of_normal p C).trans_eq hodd)
  have hcharC := centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot
    (inferInstance : Group.IsSolvable C) hoddC
  obtain ⟨T, hT⟩ := hX.exists_sylow_normalizer
  let R := (pCore p C).map C.subtype
  have hRnormal : R.Normal := inferInstance
  have hRT : R ≤ (T : Subgroup N) :=
    (pCore_isPGroup.map C.subtype).le_sylow_of_normal T
  have mem_X (r : C) (hr : r ∈ pCore p C) : ((r : N) : G) ∈ X := by
    have hrT := hRT (Subgroup.mem_map_of_mem C.subtype hr)
    have hrP := Subgroup.mem_map_of_mem N.subtype hrT
    rw [hT] at hrP
    have hrC : ((r : N) : G) ∈ Subgroup.centralizer (X : Set G) := by
      have := r.property
      change (r : N) ∈ X.normalizerMonoidHom.ker at this
      rwa [Subgroup.normalizerMonoidHom_ker] at this
    exact hc ⟨hrP.1, hrC⟩
  have hCtop : pCore p C = ⊤ := by
    apply top_unique
    intro c _
    apply hcharC
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hcC : ((c : N) : G) ∈ Subgroup.centralizer (X : Set G) := by
      have := c.property
      change (c : N) ∈ X.normalizerMonoidHom.ker at this
      rwa [Subgroup.normalizerMonoidHom_ker] at this
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcC _ (mem_X r hr)
  have hCp : IsPGroup p C := by
    have h := pCore_isPGroup (p := p) (G := C)
    rw [hCtop] at h
    exact h.of_equiv Subgroup.topEquiv
  have hCT : C ≤ (T : Subgroup N) := hCp.le_sylow_of_normal T
  intro c hcC
  have hcN := Subgroup.centralizer_le_normalizer (X : Set G) hcC
  have hcKer : (⟨c, hcN⟩ : N) ∈ C := by
    change (⟨c, hcN⟩ : N) ∈ X.normalizerMonoidHom.ker
    rwa [Subgroup.normalizerMonoidHom_ker]
  have hcP := Subgroup.mem_map_of_mem N.subtype (hCT hcKer)
  rw [hT] at hcP
  exact hc ⟨hcP.1, hcC⟩

/-- In particular, the kernel of the actual normalizer action is a p-group. -/
public theorem normalizer_action_kernel_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (X : Subgroup G) (hX : HuppertExtremal P X)
    (hc : subgroupCentralizerIn (P : Subgroup G) X ≤ X)
    (hsolv : Group.IsSolvable (Subgroup.normalizer (X : Set G)))
    (hodd : pPrimeCore p (Subgroup.normalizer (X : Set G)) = ⊥) :
    IsPGroup p X.normalizerMonoidHom.ker := by
  rw [Subgroup.normalizerMonoidHom_ker]
  exact ((IsPGroup.to_le P.isPGroup' hX.1).to_le
    (centralizer_le_of_extremal_centric P X hX hc hsolv hodd)).comap_subtype

/-- The normalizer p-core is counted by the actual action kernel and the
p-core of the actual automizer, rather than the full automorphism group. -/
public theorem normalizerPCore_card_eq
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (X : Subgroup G) (hX : HuppertExtremal P X)
    (hc : subgroupCentralizerIn (P : Subgroup G) X ≤ X)
    (hsolv : Group.IsSolvable (Subgroup.normalizer (X : Set G)))
    (hodd : pPrimeCore p (Subgroup.normalizer (X : Set G)) = ⊥) :
    Nat.card (normalizerPCore p X) =
      Nat.card X.normalizerMonoidHom.ker *
        Nat.card (pCore p X.normalizerMonoidHom.range) := by
  rw [normalizerPCore, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hker := normalizer_action_kernel_isPGroup P X hX hc hsolv hodd
  have h := X.normalizerMonoidHom.rangeRestrict.card_pCore_of_ker_isPGroup (p := p)
    X.normalizerMonoidHom.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
  simpa only [MonoidHom.ker_rangeRestrict] using h

/-- If the center has p-group automorphisms and the actual conjugation
kernel is a p-group, every subgroup acting trivially modulo the center
lies in the normalizer p-core. -/
public theorem le_normalizerPCore_of_central_quotient_trivial
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (X R : Subgroup G) (hX : IsPGroup p X)
    (hker : IsPGroup p X.normalizerMonoidHom.ker)
    (hZAut : IsPGroup p (MulAut (Subgroup.center X)))
    (hRN : R ≤ Subgroup.normalizer (X : Set G))
    (htriv : ∀ g : G, g ∈ R → ∀ x : G, x ∈ X →
      ∀ y : G, y ∈ X →
        y * (x⁻¹ * (g * x * g⁻¹)) = (x⁻¹ * (g * x * g⁻¹)) * y) :
    R ≤ normalizerPCore p X := by
  let N := Subgroup.normalizer (X : Set G)
  let f := (Subgroup.quotientAut (Subgroup.center X)).comp X.normalizerMonoidHom
  have hk : IsPGroup p f.ker :=
    (Subgroup.isPGroup_quotientAut_kernel_of_mulAut (Subgroup.center X)
      (hX.to_subgroup _) hZAut).comap_of_ker_isPGroup X.normalizerMonoidHom hker
  have hkle : f.ker ≤ pCore p N := le_sSup ⟨inferInstance, hk⟩
  intro g hg
  let gN : N := ⟨g, hRN hg⟩
  have hgk : gN ∈ f.ker := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    change Subgroup.quotientAut (Subgroup.center X) (X.normalizerMonoidHom gN)
      (QuotientGroup.mk' (Subgroup.center X) x) = QuotientGroup.mk' (Subgroup.center X) x
    rw [Subgroup.quotientAut_apply_mk]
    symm
    apply QuotientGroup.eq.mpr
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact htriv g hg x x.property y y.property
  exact Subgroup.mem_map_of_mem N.subtype (hkle hgk)

end ABG
