module
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Action
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Nontrivial.Orbit

/-!
# Nontriviality of the actual section centralizer in 12.8.11(6)

Let F₀ be the full inverse image in U of C_{U/Z(U)}(X). First exclude the
collapsed natural section W=E by the Sylow-invariant orbit argument. If a
fixed lift lies outside W, the surjective commutator map gives W=Z(U)E.
An internally lifted transposition of the marked plane gives X=Z(U)^g E.
Since E is abelian, E centralizes X, making all of U fixed; the exact
kernel C_X(U/Z(U))=E then contradicts W≠E. Thus F₀≤W.

Now [X,F₀]≤Z(U)∩X≤Z(U)^g V₂. The same internally constructed element
interchanges W and X, the two centers, and preserves E, so it transports
F₀ into X with displacement on W bounded by Z(U)V₂. Clause (4) supplies
a lift outside E, and the exact action kernel proves its transported
image is nonidentity in H/ker(ρ). Membership is checked using the literal
quotient of U/Z(U) by V₂hat from LowRank.Action.

The full plane action, commutator surjectivity, kernel, Frattini and center
identities remain explicit preceding-source inputs; the sibling (4) also
remains explicit. Their discharge belongs to the section assembly owner.
No action of all of U on U^g is introduced. The original marked g need
not lie in I₂, have square in H, or interchange U and U^g.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.11(6), printed pp.854–855 / PDF pp.871–872.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem conjugate_mul (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_U_of_point (F : InvariantFlag T V n) (a b : G)
    (he : conjugate (F.Vi 1) a = conjugate (F.Vi 1) b) :
    conjugate F.U a = conjugate F.U b := by
  have hp : conjugate (F.Vi 1) (a * b⁻¹) = F.Vi 1 := by
    rw [conjugate_mul, he]
    simpa using conjugate_conjugate_inv (F.Vi 1) b⁻¹
  have hH : a * b⁻¹ ∈ F.H := (conjugate_eq_iff _ _).mp hp
  have hU : conjugate F.U (a * b⁻¹) = F.U := (conjugate_eq_iff _ _).mpr
    (le_normalizer_conjugateSpanBy V F.H hH)
  have heU := congrArg (fun A : Subgroup G => conjugate A b) hU
  rw [← conjugate_mul, inv_mul_cancel_right] at heU
  exact heU

/-- Lift the point transposition in the full plane action to I₂. The lift itself
need not be an involution: its two conjugation equations follow on the nose
from the marked points and H-normality of U. -/
theorem exists_internal_interchange (F : InvariantFlag T V n)
    [IsKleinFour (F.Vi 2)] (L : Subgroup G) (g : G) (hg : g ∈ F.Gi 2)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hI : F.I₂ L ≤ F.Gi 2)
    (hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hI))) :
    ∃ s ∈ F.I₂ L,
      conjugate F.U s = conjugate F.U g ∧
      conjugate (conjugate F.U g) s = F.U ∧
      conjugate F.W s = F.X g ∧ conjugate (F.X g) s = F.W ∧
      conjugate F.ZU s = conjugate F.ZU g ∧
      conjugate (conjugate F.ZU g) s = F.ZU ∧
      conjugate (F.E g) s = F.E g := by
  classical
  have hz2 : z ∈ F.Vi 2 := F.monotone (by omega : 1 ≤ 2) (hz ▸ mem_zpowers z)
  let z₀ : F.Vi 2 := ⟨z, hz2⟩
  let z₁ : F.Vi 2 := (F.Vi 2).normalizerMonoidHom ⟨g⁻¹, (F.Gi 2).inv_mem hg⟩ z₀
  have h₀ : z₀ ≠ 1 := fun he => hne (congrArg Subtype.val he)
  have h₁ : z₁ ≠ 1 := by
    intro he
    apply h₀
    exact ((F.Vi 2).normalizerMonoidHom ⟨g⁻¹, (F.Gi 2).inv_mem hg⟩).injective
      (he.trans (map_one _).symm)
  let a : MulAut (F.Vi 2) := IsKleinFour.mulEquiv (Equiv.swap z₀ z₁)
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm h₀) (Ne.symm h₁))
  obtain ⟨t, ht⟩ := hfull a
  let s : G := (t : G)⁻¹
  have hsI : s ∈ F.I₂ L := (F.I₂ L).inv_mem t.property
  have hsz : (MulAut.conj s⁻¹) z = (MulAut.conj g⁻¹) z := by
    have he := congrArg (fun e : MulAut (F.Vi 2) => (e z₀ : G)) ht
    change (t : G) * z * (t : G)⁻¹ = ((Equiv.swap z₀ z₁) z₀ : G) at he
    rw [Equiv.swap_apply_left] at he
    simpa [s, z₀, z₁, MulAut.conj_apply] using he
  have hszg : (MulAut.conj s⁻¹) ((MulAut.conj g⁻¹) z) = z := by
    have he := congrArg (fun e : MulAut (F.Vi 2) => (e z₁ : G)) ht
    change (t : G) * (z₁ : G) * (t : G)⁻¹ = ((Equiv.swap z₀ z₁) z₁ : G) at he
    rw [Equiv.swap_apply_right] at he
    simpa [s, z₀, z₁, MulAut.conj_apply] using he
  have hp : conjugate (F.Vi 1) s = conjugate (F.Vi 1) g := by
    simp only [hz, conjugate, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]
    rw [hsz]
  have hpg : conjugate (conjugate (F.Vi 1) g) s = F.Vi 1 := by
    simp only [hz, conjugate, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]
    rw [hszg]
  have hU := conjugate_U_of_point F s g hp
  have hUg : conjugate (conjugate F.U g) s = F.U := by
    have hH : g * s ∈ F.H := (conjugate_eq_iff _ _).mp
      ((conjugate_mul _ _ _).trans hpg)
    rw [← conjugate_mul]
    exact (conjugate_eq_iff _ _).mpr (le_normalizer_conjugateSpanBy V F.H hH)
  have hc (k : G) (hk : k ∈ F.Gi 2) :
      conjugate (centralizer (F.Vi 2 : Set G)) k = centralizer (F.Vi 2 : Set G) :=
    (conjugate_eq_iff _ _).mpr (normalizer_le_normalizer_centralizer _ hk)
  have hW : conjugate F.W s = F.X g := by
    change conjugate (F.U ⊓ centralizer (F.Vi 2 : Set G)) s =
      conjugate (F.U ⊓ centralizer (F.Vi 2 : Set G)) g
    rw [conjugate_inf, conjugate_inf, hU, hc s (hI hsI), hc g hg]
  have hX : conjugate (F.X g) s = F.W := by
    change conjugate (conjugate (F.U ⊓ centralizer (F.Vi 2 : Set G)) g) s = _
    rw [conjugate_inf, hc g hg, conjugate_inf, hUg, hc s (hI hsI)]
    rfl
  have hZ : conjugate F.ZU s = conjugate F.ZU g := by
    change conjugate (centerIn F.U) s = conjugate (centerIn F.U) g
    rw [← centerIn_conjugate, ← centerIn_conjugate, hU]
  have hZg : conjugate (conjugate F.ZU g) s = F.ZU := by
    change conjugate (conjugate (centerIn F.U) g) s = centerIn F.U
    rw [← centerIn_conjugate, ← centerIn_conjugate, hUg]
  refine ⟨s, hsI, hU, hUg, hW, hX, hZ, hZg, ?_⟩
  change conjugate (F.W ⊓ F.X g) s = F.W ⊓ F.X g
  rw [conjugate_inf, hW, hX, inf_comm]

/-- The full inverse image of the common fixed space in the original U. -/
def fixedLift (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) : Subgroup G :=
  (((XfixedSpace F ρ g).toAddSubgroup.toSubgroup').comap
    (QuotientGroup.mk' (center F.U))).map F.U.subtype

theorem fixedLift_le_U (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) : fixedLift F ρ g ≤ F.U :=
  map_subtype_le _

theorem mem_fixedLift_iff (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) (u : F.U) :
    (u : G) ∈ fixedLift F ρ g ↔
      Additive.ofMul (QuotientGroup.mk' (center F.U) u) ∈ XfixedSpace F ρ g := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hev : v = u := Subtype.ext he
    exact hev ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- The fixed-space definition gives the actual ambient commutator bound,
before any normalization of X by the lift has been asserted. -/
theorem commutator_X_fixedLift_le_ZU (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (g : G) (hg : g ∈ F.Gi 2) :
    ⁅F.X g, fixedLift F ρ g⁆ ≤ F.ZU := by
  apply commutator_le.mpr
  intro x hx u hu
  let xH : F.H := ⟨x, F.X_le_H g hg hx⟩
  let uU : F.U := ⟨u, fixedLift_le_U F ρ g hu⟩
  have he := (mem_XfixedSpace_iff F ρ g _).mp
    ((mem_fixedLift_iff F ρ g uU).mp hu)
    (QuotientGroup.mk' ρ.ker xH) ⟨xH, hx, rfl⟩
  have heq := congrArg Additive.toMul he
  change ρ xH (QuotientGroup.mk' (center F.U) uU) =
    QuotientGroup.mk' (center F.U) uU at heq
  rw [hρ] at heq
  have hc := QuotientGroup.eq_iff_div_mem.mp heq
  refine ⟨(F.U.normalizerMonoidHom
    ⟨xH, le_normalizer_conjugateSpanBy V F.H xH.property⟩ uU) / uU, hc, ?_⟩
  simp only [div_eq_mul_inv, commutatorElement_def]
  rfl

/-- The source's first displacement bound once placement in W has been proved.
Only W, rather than all of U, is used to normalize the conjugate subgroup. -/
theorem commutator_X_fixedLift_le_intersection (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (g : G) (hg : g ∈ F.Gi 2)
    (hplace : fixedLift F ρ g ≤ F.W) :
    ⁅F.X g, fixedLift F ρ g⁆ ≤ F.ZU ⊓ F.X g := by
  exact le_inf (commutator_X_fixedLift_le_ZU F ρ hρ g hg)
    (le_normalizer_iff_commutator_le_left.mp
      ((hplace.trans inf_le_right).trans (F.plane_centralizer_normalizes_actors g hg).1))

/-- Clause (4) and strict containment provide a lift genuinely outside E. -/
theorem exists_fixedLift_not_mem_E (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat) (g : G)
    (hfour : hatSpace F (F.E g) ⊓ XfixedSpace F ρ g = hatSpace F (F.Vi 2))
    (hstrict : hatSpace F (F.Vi 2) < XfixedSpace F ρ g) :
    ∃ u ∈ fixedLift F ρ g, u ∉ F.E g := by
  have hnot : ¬ XfixedSpace F ρ g ≤ hatSpace F (F.Vi 2) := not_le_of_gt hstrict
  obtain ⟨v, hv, hvl⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) v.toMul
  have huf : (u : G) ∈ fixedLift F ρ g := by
    apply (mem_fixedLift_iff F ρ g u).mpr
    simpa only [hu, ofMul_toMul] using hv
  refine ⟨u, huf, fun hue => hvl ?_⟩
  rw [← hfour]
  exact ⟨⟨u, hue, hu⟩, hv⟩

private theorem quotient_mem_hatImage_of_mem_sup (F : InvariantFlag T V n)
    (A : Subgroup G) (hA : A ≤ F.U) (u : F.U) (hu : (u : G) ∈ F.ZU ⊔ A) :
    QuotientGroup.mk' (center F.U) u ∈ hatImage F A := by
  let C := ((hatImage F A).comap (QuotientGroup.mk' (center F.U))).map F.U.subtype
  have hZ : F.ZU ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    change QuotientGroup.mk' (center F.U) z ∈ hatImage F A
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
    exact (hatImage F A).one_mem
  have hAC : A ≤ C := by
    intro a ha
    exact ⟨⟨a, hA ha⟩, ⟨⟨a, hA ha⟩, ha, rfl⟩, rfl⟩
  obtain ⟨v, hv, he⟩ := (sup_le hZ hAC) hu
  have hev : v = u := Subtype.ext he
  exact hev ▸ hv

/-- Ambient displacement modulo Z(U)V₂ gives membership in the literal
section centralizer. This retains both quotient maps and the action equation. -/
theorem mem_Xdot₀_of_displacement (F : InvariantFlag T V n)
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (g : G) (hg : g ∈ F.Gi 2) (x : G) (hx : x ∈ F.X g)
    (hmove : ∀ w ∈ F.W, ⁅x, w⁆ ∈ F.ZU ⊔ F.Vi 2) :
    QuotientGroup.mk' ρ.ker ⟨x, F.X_le_H g hg hx⟩ ∈ Xdot₀ F ρ g := by
  let xH : F.H := ⟨x, F.X_le_H g hg hx⟩
  apply (mem_Xdot₀_iff F ρ hρ g hg _).mpr
  refine ⟨⟨xH, hx, rfl⟩, ?_⟩
  intro w hw
  obtain ⟨u, hu, he⟩ := (show w.toMul ∈ hatImage F F.W from hw)
  apply (Submodule.Quotient.eq _).mpr
  rw [← ofMul_toMul w, ← he, dotLinearAction_mk_apply, hρ]
  let v := F.U.normalizerMonoidHom
    ⟨xH, le_normalizer_conjugateSpanBy V F.H xH.property⟩ u
  have hmem := quotient_mem_hatImage_of_mem_sup F (F.Vi 2)
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) (v / u)
    (show (v / u : F.U).val ∈ F.ZU ⊔ F.Vi 2 by
      change x * (u : G) * x⁻¹ / (u : G) ∈ _
      simpa only [commutatorElement_def, div_eq_mul_inv] using hmove u hu)
  change QuotientGroup.mk' (center F.U) v / QuotientGroup.mk' (center F.U) u ∈ hatImage F (F.Vi 2)
  simpa only [map_div] using hmem

/-- The nontriviality argument, with the fixed-lift placement isolated.
All conjugation is performed by the internally constructed interchange; the
only kernel used is C_X(U/Z(U))=E from 12.8.9(5). The placement premise is
not part of the source statement and must be discharged in final assembly. -/
theorem Xdot₀_ne_bot_of_fixedLift_le_W (F : InvariantFlag T V n)
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat] [IsKleinFour (F.Vi 2)]
    (L : Subgroup G) (g : G) (hg : g ∈ F.Gi 2)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hI : F.I₂ L ≤ F.Gi 2)
    (hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hI)))
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (hkernel : F.X g ⊓ ρ.ker.map F.H.subtype = F.E g)
    (hcenter : F.ZU ⊓ conjugate F.U g =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hfour : hatSpace F (F.E g) ⊓ XfixedSpace F ρ g = hatSpace F (F.Vi 2))
    (hplace : fixedLift F ρ g ≤ F.W)
    (hstrict : hatSpace F (F.Vi 2) < XfixedSpace F ρ g) :
    Xdot₀ F ρ g ≠ ⊥ := by
  obtain ⟨s, hs, _, _, hW, hX, _, hZg, hE⟩ :=
    exists_internal_interchange F L g hg z hz hne hI hfull
  have hbound : ⁅F.X g, fixedLift F ρ g⁆ ≤ conjugate F.ZU g ⊔ F.Vi 2 := by
    calc
      ⁅F.X g, fixedLift F ρ g⁆ ≤ F.ZU ⊓ F.X g :=
        commutator_X_fixedLift_le_intersection F ρ hρ g hg hplace
      _ ≤ F.ZU ⊓ conjugate F.U g := inf_le_inf_left _ (map_mono inf_le_left)
      _ = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 := hcenter
      _ ≤ conjugate F.ZU g ⊔ F.Vi 2 := sup_le_sup inf_le_right
        (F.monotone (by omega))
  have htransport : ⁅conjugate (fixedLift F ρ g) s, F.W⁆ ≤ F.ZU ⊔ F.Vi 2 := by
    have hm := map_mono hbound (f := (MulAut.conj s⁻¹).toMonoidHom)
    change conjugate ⁅F.X g, fixedLift F ρ g⁆ s ≤
      conjugate (conjugate F.ZU g ⊔ F.Vi 2) s at hm
    have hc (A B : Subgroup G) : conjugate ⁅A, B⁆ s = ⁅conjugate A s, conjugate B s⁆ :=
      map_commutator A B _
    have hsup (A B : Subgroup G) : conjugate (A ⊔ B) s = conjugate A s ⊔ conjugate B s :=
      Subgroup.map_sup _ _ _
    rw [hc, hsup, hX, hZg, (conjugate_eq_iff _ _).mpr (hI hs), commutator_comm] at hm
    exact hm
  obtain ⟨u, hu, hue⟩ := exists_fixedLift_not_mem_E F ρ g hfour hstrict
  let x := (MulAut.conj s⁻¹) u
  have hxA : x ∈ conjugate (fixedLift F ρ g) s := ⟨u, hu, rfl⟩
  have hx : x ∈ F.X g := hW ▸ (map_mono hplace hxA)
  have hxe : x ∉ F.E g := by
    intro he
    rw [← hE] at he
    obtain ⟨v, hv, hve⟩ := he
    exact hue (((MulAut.conj s⁻¹).injective hve) ▸ hv)
  have hsec := mem_Xdot₀_of_displacement F ρ hρ g hg x hx
    (fun w hw => htransport (commutator_mem_commutator hxA hw))
  intro hbot
  have he : QuotientGroup.mk' ρ.ker ⟨x, F.X_le_H g hg hx⟩ = 1 := by
    exact mem_bot.mp (hbot ▸ hsec)
  apply hxe
  rw [← hkernel]
  exact ⟨hx, ⟨⟨x, F.X_le_H g hg hx⟩, (QuotientGroup.eq_one_iff _).mp he, rfl⟩⟩

theorem ZU_le_fixedLift (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) : F.ZU ≤ fixedLift F ρ g := by
  rintro _ ⟨u, hu, rfl⟩
  apply (mem_fixedLift_iff F ρ g u).mpr
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr hu]
  exact (XfixedSpace F ρ g).zero_mem

private theorem centralizer_le_fixedLift (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (g : G) : F.U ⊓ centralizer (F.X g : Set G) ≤ fixedLift F ρ g := by
  rintro u ⟨hu, hc⟩
  apply (mem_fixedLift_iff F ρ g ⟨u, hu⟩).mpr
  apply (mem_XfixedSpace_iff F ρ g _).mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [dotLinearAction_mk_apply, hρ]
  have he : F.U.normalizerMonoidHom
      ⟨x, le_normalizer_conjugateSpanBy V F.H x.property⟩ ⟨u, hu⟩ = ⟨u, hu⟩ := by
    apply Subtype.ext
    change (x : G) * u * (x : G)⁻¹ = u
    exact mul_inv_eq_iff_eq_mul.mpr (hc x hx)
  rw [he]

private theorem fixedLift_eq_U_of_outside (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat) (g : G)
    (hindex : F.W.relIndex F.U = 2) (hW : F.W ≤ fixedLift F ρ g)
    (u : G) (hu : u ∈ fixedLift F ρ g) (hun : u ∉ F.W) :
    fixedLift F ρ g = F.U := by
  apply le_antisymm (fixedLift_le_U F ρ g)
  intro y hy
  by_cases hyW : y ∈ F.W
  · exact hW hyW
  · let uU : F.U := ⟨u, fixedLift_le_U F ρ g hu⟩
    let yU : F.U := ⟨y, hy⟩
    have hi : (F.W.subgroupOf F.U).index = 2 := hindex
    have hc : y * u⁻¹ ∈ F.W :=
      (mul_mem_iff_of_index_two hi (a := yU) (b := uU⁻¹)).mpr
        (iff_of_false hyW (by
          change u⁻¹ ∉ F.W
          simpa using hun))
    have he := (fixedLift F ρ g).mul_mem (hW hc) hu
    simpa only [inv_mul_cancel_right] using he

/-- The full fixed lift is contained in W as soon as the zero natural-module
case W=E has been excluded. The natural-module input is the literal
surjectivity [X,u]E=W for each u outside W, not a dimension surrogate. -/
theorem fixedLift_le_W_of_noncollapsed (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] [IsKleinFour (F.Vi 2)]
    (L : Subgroup G) (g : G) [IsMulCommutative (F.E g)] (hg : g ∈ F.Gi 2)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hI : F.I₂ L ≤ F.Gi 2)
    (hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hI)))
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (hkernel : F.X g ⊓ ρ.ker.map F.H.subtype = F.E g)
    (hindex : F.W.relIndex F.U = 2)
    (hmove : ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x, u⁆ * e = w)
    (hproper : F.W ≠ F.E g) :
    fixedLift F ρ g ≤ F.W := by
  intro u hu
  by_contra hun
  have hUZ := commutator_X_fixedLift_le_ZU F ρ hρ g hg
  have hW : F.W ≤ F.ZU ⊔ F.E g := by
    intro w hw
    obtain ⟨x, hx, e, he, rfl⟩ := hmove u (fixedLift_le_U F ρ g hu) hun w hw
    exact mul_mem (mem_sup_left (hUZ (commutator_mem_commutator hx hu)))
      (mem_sup_right he)
  obtain ⟨s, _, _, _, hWs, _, hZs, _, hEs⟩ :=
    exists_internal_interchange F L g hg z hz hne hI hfull
  have hX : F.X g ≤ conjugate F.ZU g ⊔ F.E g := by
    have hm := map_mono hW (f := (MulAut.conj s⁻¹).toMonoidHom)
    change conjugate F.W s ≤ conjugate (F.ZU ⊔ F.E g) s at hm
    have hsup : conjugate (F.ZU ⊔ F.E g) s =
        conjugate F.ZU s ⊔ conjugate (F.E g) s := Subgroup.map_sup _ _ _
    rwa [hWs, hsup, hZs, hEs] at hm
  have hZE : conjugate F.ZU g ≤ centralizer (F.E g : Set G) := by
    have hZ : F.ZU ≤ centralizer (F.U : Set G) := by
      rintro _ ⟨a, ha, rfl⟩ b hb
      exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b, hb⟩)
    exact ((map_mono hZ).trans (map_centralizer_le_centralizer_image _ _)).trans
      (centralizer_le (show F.E g ≤ conjugate F.U g from inf_le_right.trans (map_mono inf_le_left)))
  have hXE : F.X g ≤ centralizer (F.E g : Set G) :=
    hX.trans (sup_le hZE (le_centralizer (F.E g)))
  have hEf : F.E g ≤ fixedLift F ρ g :=
    (le_inf (inf_le_left.trans inf_le_left) (le_centralizer_iff.mp hXE)).trans
      (centralizer_le_fixedLift F ρ hρ g)
  have hWf : F.W ≤ fixedLift F ρ g := hW.trans (sup_le (ZU_le_fixedLift F ρ g) hEf)
  have hall := fixedLift_eq_U_of_outside F ρ g hindex hWf u hu hun
  have hXE' : F.X g ≤ F.E g := by
    intro x hx
    rw [← hkernel]
    refine ⟨hx, ?_⟩
    let xH : F.H := ⟨x, F.X_le_H g hg hx⟩
    refine ⟨xH, ?_, rfl⟩
    apply MulEquiv.ext
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center F.U) q
    have hv : (v : G) ∈ fixedLift F ρ g := hall.symm ▸ v.property
    have he := (mem_XfixedSpace_iff F ρ g _).mp
      ((mem_fixedLift_iff F ρ g v).mp hv)
      (QuotientGroup.mk' ρ.ker xH) ⟨xH, hx, rfl⟩
    exact congrArg Additive.toMul he
  have heq : F.X g = F.E g := le_antisymm hXE' inf_le_right
  have hc : Nat.card (F.X g) = Nat.card F.W :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  apply hproper
  apply (eq_of_le_of_card_ge (show F.E g ≤ F.W from inf_le_left) ?_).symm
  rw [← heq, hc]

/-- The group-theoretic nontriviality step of 12.8.11(6).

The explicit premises are earlier 12.8.4 (nonabelian two-group U and its
Frattini line), 12.8.9 (the full parabolic plane action, the marked natural
commutator image, and C_X(Uhat)=E), 12.8.10(1), and sibling 12.8.11(4).
The elementary intersection, its properness in W, fixed-lift placement and
internal interchange are all proved here or by the published (2) proof.
-/
theorem Xdot₀_ne_bot_of_fixedSpace_lt (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 (F.Vi 2)]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hUnon : ¬ IsMulCommutative F.U) (hUtwo : IsPGroup 2 F.U)
    (hPhi : (frattini F.U).map F.U.subtype = F.Vi 1)
    (L : Subgroup G) (g : G) (hg : g ∈ F.Gi 2)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hI : F.I₂ L ≤ F.Gi 2)
    (hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hI)))
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (hkernel : F.X g ⊓ ρ.ker.map F.H.subtype = F.E g)
    (hindex : F.W.relIndex F.U = 2)
    (hmove : ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x, u⁆ * e = w)
    (hcenter : F.ZU ⊓ conjugate F.U g =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hfour : hatSpace F (F.E g) ⊓ XfixedSpace F ρ g = hatSpace F (F.Vi 2))
    (hstrict : hatSpace F (F.Vi 2) < XfixedSpace F ρ g) :
    Xdot₀ F ρ g ≠ ⊥ := by
  have hc : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 hn
  let : Nontrivial (F.Vi 2) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (F.Vi 2) := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  let : IsElementaryAbelian 2 (F.E g) :=
    F.E_elementary (by omega) g hUtwo hPhi hdis
  have hplace := fixedLift_le_W_of_noncollapsed F L g hg z hz hne hI hfull
    ρ hρ hkernel hindex hmove (W_ne_E F g hUnon hindex)
  exact Xdot₀_ne_bot_of_fixedLift_le_W F L g hg z hz hne hI hfull
    ρ hρ hkernel hcenter hfour hplace hstrict

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
