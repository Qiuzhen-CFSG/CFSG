module

public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Products
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# Direct-power sections of local component orbits

Commuting conjugates of a subgroup of characteristic p give a central product.
The kernel of the multiplication map from their direct product is central,
hence a p-group. Factoring by the full p-core therefore gives a direct power
of the original p-core quotient. Adjoining a p-subgroup retains a normal base
with p-group upper quotient, without assuming either extension splits.

This is the central-cover form of the component-orbit argument used in
Aschbacher–Smith, 2.3.9(7), printed p.526. Component subnormality may be relative
to an overgroup, and only the component stabilizer need preserve the seed.
-/

public section
noncomputable section
open Subgroup
namespace Theory.GroupTheory.ComponentLocalCoreSection

variable {E F : Type*} [Group E] [Group F]

/-- A p-group kernel preserves the quotient by the full p-core. -/
def quotientCoreEquiv [Finite E] [Finite F] (p : ℕ) [Fact p.Prime]
    (f : E →* F) (hf : Function.Surjective f) (hp : IsPGroup p f.ker) :
    (E ⧸ pCore p E) ≃* (F ⧸ pCore p F) := by
  let q := (QuotientGroup.mk' (pCore p F)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have hk : q.ker = pCore p E := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hp
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

private theorem quotient_core_bot [Finite E] (p : ℕ) [Fact p.Prime] :
    pCore p (E ⧸ pCore p E) = ⊥ := by
  let q := QuotientGroup.mk' (pCore p E)
  have hq := QuotientGroup.mk'_surjective (pCore p E)
  have hk : IsPGroup p q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hm := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hq hk)
  rw [map_comap_eq_self_of_surjective hq] at hm
  exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

private theorem power_core_bot (p : ℕ) (I : Type*) (hF : pCore p F = ⊥) :
    pCore p (I → F) = ⊥ := by
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  funext i
  let ev := Pi.evalMonoidHom (fun _ : I => F) i
  have hev : Function.Surjective ev := fun y => ⟨fun _ => y, rfl⟩
  have hle : (pCore p (I → F)).map ev ≤ pCore p F :=
    le_sSup ⟨Subgroup.Normal.map inferInstance ev hev, pCore_isPGroup.map ev⟩
  have hi := hle (mem_map_of_mem ev hx)
  exact mem_bot.mp (hF ▸ hi)

/-- The p-core quotient commutes with finite direct powers. -/
def quotientCorePowerEquiv [Finite E] (p : ℕ) [Fact p.Prime]
    (I : Type*) [Finite I] :
    ((I → E) ⧸ pCore p (I → E)) ≃* (I → E ⧸ pCore p E) := by
  let q := QuotientGroup.mk' (pCore p E)
  have hk : IsPGroup p q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  apply Classical.choice
  obtain ⟨f, hf, hp⟩ := power_surjection_kernel_isPGroup (I := I) q
    (QuotientGroup.mk'_surjective _) hk
  have hkf : f.ker = pCore p (I → E) := by
    have he := f.comap_pCore_of_ker_isPGroup hf hp
    rwa [power_core_bot p I (quotient_core_bot p), MonoidHom.comap_bot] at he
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkf.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- A homomorphism injective on each direct factor has central kernel. -/
theorem ker_le_center_of_injective_factors {I : Type*} [DecidableEq I]
    {D : I → Type*} [∀ i, Group (D i)] (f : (∀ i, D i) →* F)
    (hinj : ∀ i, Function.Injective (f.comp (MonoidHom.mulSingle D i))) :
    f.ker ≤ center (∀ i, D i) := by
  intro x hx
  rw [mem_center_iff]
  intro y
  funext i
  have hi : x * Pi.mulSingle i (y i) * x⁻¹ =
      Pi.mulSingle i (x i * y i * (x i)⁻¹) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.mulSingle_eq_of_ne hji]
  have he : f (Pi.mulSingle i (x i * y i * (x i)⁻¹)) = f (Pi.mulSingle i (y i)) := by
    rw [← hi, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hx]
    simp
  have he' := hinj i he
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

end Theory.GroupTheory.ComponentLocalCoreSection

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The full p-core quotient of the seed orbit is an actual direct power.
Nontrivial intersections of factors remain in the p-core of the central product. -/
theorem IsComponent.local_orbit_quotient_core_equiv_power
    {p : ℕ} [Fact p.Prime] {L K A : Subgroup G}
    (hL : IsComponent G L) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hself : centralizer (pCore p K : Set K) ≤ pCore p K) :
    ∃ n : ℕ, Nonempty (((componentOrbit K A) ⧸ pCore p (componentOrbit K A)) ≃*
      (Fin n → K ⧸ pCore p K)) := by
  classical
  let F := fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom
  let I := {T : Subgroup G // T ∈ Set.range F}
  let a : I → A := fun i => Classical.choose i.property
  have ha (i : I) : F (a i) = i.val := Classical.choose_spec i.property
  have hcomm : Pairwise fun i j : I => ∀ x y : G,
      x ∈ i.val → y ∈ j.val → Commute x y := by
    intro i j hij x y hx hy
    rcases hL.local_conjugates_eq_or_commute hKL hinv (a j) (a i) with he | hc
    · exact (hij (Subtype.ext ((ha i).symm.trans (he.trans (ha j))))).elim
    · have hc' : ⁅i.val, j.val⁆ = ⊥ := by simpa only [← ha i, ← ha j] using hc
      exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc') hx) y hy).symm
  let : Fintype I := Fintype.ofFinite I
  let f₀ := noncommPiCoprod hcomm
  have hr : f₀.range = componentOrbit K A := by
    rw [noncommPiCoprod_range]
    apply le_antisymm
    · apply iSup_le
      rintro ⟨T, b, rfl⟩
      exact le_iSup F b
    · exact iSup_le fun b => le_iSup (fun i : I => i.val) ⟨F b, b, rfl⟩
  let f : (∀ i : I, i.val) →* componentOrbit K A :=
    (MulEquiv.subgroupCongr hr).toMonoidHom.comp f₀.rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hr).surjective.comp f₀.rangeRestrict_surjective
  have hfi : ∀ i, Function.Injective (f.comp (MonoidHom.mulSingle (fun i : I => i.val) i)) := by
    intro i x y hxy
    have he := congrArg (fun t : componentOrbit K A => (t : G)) hxy
    change f₀ (Pi.mulSingle i x) = f₀ (Pi.mulSingle i y) at he
    simpa only [f₀, noncommPiCoprod_mulSingle, Subtype.val_inj] using he
  let ei : (I → K) ≃* (∀ i : I, i.val) := MulEquiv.piCongrRight fun i =>
    ((MulAut.conj (a i : G)).subgroupMap K).trans (MulEquiv.subgroupCongr (ha i))
  have hchar : centralizer (pCore p (∀ i : I, i.val) : Set (∀ i : I, i.val)) ≤
      pCore p (∀ i : I, i.val) :=
    (Theory.Quasithin.centralizer_pCore_le_iff p ei).mp (centralizer_pCore_power_le hself)
  have hker : f.ker ≤ pCore p (∀ i : I, i.val) := by
    intro x hx
    apply hchar
    intro y _
    exact mem_center_iff.mp (ComponentLocalCoreSection.ker_le_center_of_injective_factors f hfi hx) y
  let eq₁ := ComponentLocalCoreSection.quotientCoreEquiv p f hf (pCore_isPGroup.to_le hker)
  let eq₂ := QuotientGroup.congr _ _ ei (pCore_map_iso p ei)
  let eq₃ := ComponentLocalCoreSection.quotientCorePowerEquiv (E := K) p I
  exact ⟨Fintype.card I, ⟨eq₁.symm.trans (eq₂.symm.trans (eq₃.trans
    (MulEquiv.arrowCongr (Fintype.equivFin I) (MulEquiv.refl _))))⟩⟩

/-- A p-subgroup acting on the component orbit gives the required normal section,
with the full p-core retained and no splitting hypothesis. -/
theorem IsComponent.local_adjoin_normalDirectPowerSection
    {p : ℕ} [Fact p.Prime] {L K A : Subgroup G} {B : Type*} [Group B]
    (hL : IsComponent G L) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hself : centralizer (pCore p K : Set K) ≤ pCore p K)
    (hA : IsPGroup p A) (e : (K ⧸ pCore p K) ≃* B) :
    Nonempty (NormalDirectPowerSection p (K ⊔ A : Subgroup G) B) := by
  let N := (componentOrbit K A).subgroupOf (K ⊔ A)
  let := componentOrbit_normal_subgroupOf_sup K A
  let eN := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  obtain ⟨n, ⟨eO⟩⟩ := hL.local_orbit_quotient_core_equiv_power hKL hinv hself
  exact ⟨{
    base := N
    normal := inferInstance
    quotient_isPGroup := local_orbit_quotient_isPGroup K A hA
    copies := n
    quotientIso := (QuotientGroup.congr _ _ eN (pCore_map_iso p eN)).trans
      (eO.trans (MulEquiv.piCongrRight fun _ => e)) }⟩

end Theory.GroupTheory

namespace Theory.GroupTheory.NormalDirectPowerSection
variable {X Y B : Type*} [Group X] [Group Y] [Group B] {p : ℕ}

/-- Transport both normal quotients along an actual group equivalence. -/
def of_mulEquiv (d : NormalDirectPowerSection p X B) (e : X ≃* Y) :
    NormalDirectPowerSection p Y B := by
  letI := d.normal
  let N := d.base.map e.toMonoidHom
  letI : N.Normal := Subgroup.Normal.map d.normal e.toMonoidHom e.surjective
  let eb := e.subgroupMap d.base
  exact {
    base := N
    normal := inferInstance
    quotient_isPGroup := d.quotient_isPGroup.of_equiv (QuotientGroup.congr d.base N e rfl)
    copies := d.copies
    quotientIso := (QuotientGroup.congr _ _ eb (pCore_map_iso p eb)).symm.trans d.quotientIso }

end Theory.GroupTheory.NormalDirectPowerSection

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The section calculation only requires component subnormality inside H.
It makes no normality assertion about H in the larger ambient group. -/
theorem IsComponent.relative_local_adjoin_normalDirectPowerSection
    {p : ℕ} [Fact p.Prime] {H L K A : Subgroup G} {B : Type*} [Group B]
    (hL : IsComponent H (L.subgroupOf H)) (hLH : L ≤ H) (hKL : K ≤ L)
    (hAH : A ≤ H) (hA : IsPGroup p A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hself : centralizer (pCore p K : Set K) ≤ pCore p K)
    (e : (K ⧸ pCore p K) ≃* B) :
    Nonempty (NormalDirectPowerSection p (K ⊔ A : Subgroup G) B) := by
  let F := K.subgroupOf H
  let D := A.subgroupOf H
  have hKH : K ≤ H := hKL.trans hLH
  have hinvH : D ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  let eF : F ≃* K := subgroupOfEquivOfLe hKH
  have hselfF : centralizer (pCore p F : Set F) ≤ pCore p F :=
    (Theory.Quasithin.centralizer_pCore_le_iff p eF).mpr hself
  let eQ := (QuotientGroup.congr _ _ eF (pCore_map_iso p eF)).trans e
  obtain ⟨d⟩ := hL.local_adjoin_normalDirectPowerSection (subgroupOf_mono H hKL)
    hinvH hselfF hA.comap_subtype eQ
  let eX : (F ⊔ D : Subgroup H) ≃* (K ⊔ A : Subgroup G) :=
    (MulEquiv.subgroupCongr (subgroupOf_sup hKH hAH).symm).trans
      (subgroupOfEquivOfLe (sup_le hKH hAH))
  exact ⟨d.of_mulEquiv eX⟩

end Theory.GroupTheory
