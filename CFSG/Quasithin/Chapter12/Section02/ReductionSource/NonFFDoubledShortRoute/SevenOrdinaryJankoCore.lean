module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJankoOrbit
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The placed A₇ orbit in the center of a normal two-core

The actual odd actor residual inherits the doubled A₇ action's trivial
invertible commutant. The original component is covered by that residual and
its own two-core, which centralizes the orbit. The residual's two-core also
acts trivially, without identifying its central-cover quotient with A₇.

After an injective native placement, commutators with an ambient two-core
lie in the residual two-core. The trivial commutant makes the ambient core
centralize the orbit. Normality places the elementary orbit inside that
core, so its actual order 256 bounds the order of the core's center.

Source: the local-module inspection in Aschbacher–Smith 4.4.3, printed
pp.622–623 of refs/quasithin.pdf, and the A₇ pair commutant in H.8, p.389.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Representation.AlternatingSevenConjugatePair.Model

private theorem mapped_core_centralizes_of_commutant
    {Q S U : Type*} [Group Q] [Group S] [Group U] [IsElementaryAbelian 2 U]
    (M : Subgroup Q) (r : S →* Q) (w : U →* Q)
    (hr : Function.Injective r) (hw : Function.Injective w)
    (hrM : r.range ≤ M) (hnr : M ≤ normalizer (r.range : Set Q))
    (hnw : M ≤ normalizer (w.range : Set Q))
    (ψ : S →* MulAut U) (hcore : pCore 2 S ≤ ψ.ker)
    (hmark : ∀ s u, w (ψ s u) = r s * w u * (r s)⁻¹)
    (hcommutant : ∀ f : Additive U ≃ₗ[ZMod 2] Additive U,
      (∀ s v, f (Additive.ofMul (ψ s v.toMul)) = Additive.ofMul (ψ s (f v).toMul)) →
      f = LinearEquiv.refl _ _) :
    M.pCoreIn 2 ≤ centralizer (w.range : Set Q) := by
  let b : U ≃* w.range := MonoidHom.ofInjective hw
  let φ : M →* MulAut U := (MulAut.congr b.symm).toMonoidHom.comp
    (w.range.normalizerMonoidHom.comp (inclusion hnw))
  have hφ (x : M) (u : U) : w (φ x u) = (x : Q) * w u * (x : Q)⁻¹ := by
    change ((b (b.symm (w.range.normalizerMonoidHom (inclusion hnw x) (b u)))) : Q) = _
    rw [b.apply_symm_apply]
    rfl
  let R := r.range.subgroupOf M
  let : R.Normal := (normal_subgroupOf_iff_le_normalizer hrM).mpr hnr
  let a : R ≃* S := (subgroupOfEquivOfLe hrM).trans (MonoidHom.ofInjective hr).symm
  have hra (x : R) : r (a x) = ((x : M) : Q) := by
    exact congrArg Subtype.val ((MonoidHom.ofInjective hr).apply_symm_apply
      ((subgroupOfEquivOfLe hrM) x))
  have hres (x : R) : φ x = ψ (a x) := by
    ext u
    apply hw
    rw [hφ,hmark,hra]
  have hk (z : R) (hz : z ∈ pCore 2 R) : φ z = 1 := by
    rw [hres]
    apply hcore
    rw [←pCore_map_iso 2 a]
    exact mem_map_of_mem _ hz
  have hkill : pCore 2 M ≤ φ.ker := by
    intro x hx
    have hc (s : S) : Commute (φ x) (ψ s) := by
      obtain ⟨y,rfl⟩ := a.surjective s
      rw [←hres]
      have hm := commutator_mem_commutator hx y.property
      have hR : ⁅x,(y : M)⁆ ∈ R := (commutator_le_right (pCore 2 M) R) hm
      have hp : ⁅x,(y : M)⁆ ∈ pCore 2 M := (commutator_le_left (pCore 2 M) R) hm
      apply commutatorElement_eq_one_iff_commute.mp
      rw [←map_commutatorElement]
      exact hk ⟨_,hR⟩ (by rw [pCore_eq_comap_of_normal]; exact hp)
    let a := (φ x).toAdditive
    let f : Additive U ≃ₗ[ZMod 2] Additive U :=
      a.toLinearEquiv (fun c v => ZMod.map_smul a.toAddMonoidHom c v)
    have hf := hcommutant f (fun s v =>
      congrArg (fun b : MulAut U => Additive.ofMul (b v.toMul)) (hc s).eq)
    change φ x = 1
    ext u
    exact congrArg Additive.toMul (LinearEquiv.congr_fun hf (Additive.ofMul u))
  rintro _ ⟨x,hx,rfl⟩ _ ⟨u,rfl⟩
  have hh := hφ x u
  have he : φ x = 1 := hkill hx
  rw [he] at hh
  change w u = (x : Q) * w u * (x : Q)⁻¹ at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem component_core_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
  apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
  simpa only [D.fundamentalSetup_module,Chapter3.Section02.localJoin,D.localOrbit_eq,
    D.sourceOrbit_eq] using (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module

private theorem residual_core_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    (oddActorResidual L A).pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨hc,_,_,_⟩ := D.doubledOrbit_oddActorResidual_cover h A
    (by simpa only [←D.sourceOrbit_eq] using hA) ho
  have hRL : oddActorResidual L A ≤ L := (oddActorResidual_le L A).trans inf_le_left
  obtain ⟨e,he⟩ := exists_pCoreQuotientEquiv_of_cover hRL hc.subset
  apply le_trans ?_ (D.component_core_centralizes h)
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨inclusion hRL x,?_,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (pCore 2 L)) (inclusion hRL x) = 1
  have hxq : QuotientGroup.mk' (pCore 2 (oddActorResidual L A)) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [←he,hxq,map_one]

private theorem residual_centralizer_eq_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (f : Additive D.sourceOrbit ≃ₗ[ZMod 2] Additive D.sourceOrbit)
    (hf : ∀ r : oddActorResidual L A, ∀ v,
      f (doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes
        (inclusion ((oddActorResidual_le L A).trans inf_le_left) r) v) =
      doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes
        (inclusion ((oddActorResidual_le L A).trans inf_le_left) r) (f v)) :
    f = LinearEquiv.refl _ _ := by
  obtain ⟨hcover,_,_,_⟩ := D.doubledOrbit_oddActorResidual_cover h A
    (by simpa only [←D.sourceOrbit_eq] using hA) ho
  have hcore := D.component_core_centralizes h
  apply D.sourceOrbit_seven_centralizer_eq_one h hd σ hσ hmodel f
  intro l v
  have hl : l.val ∈ (oddActorResidual L A : Set G) * (L.pCoreIn 2 : Set G) :=
    hcover ▸ l.property
  obtain ⟨r,hr,c,hc,he⟩ := hl
  let rL : L := ⟨r,(oddActorResidual_le L A hr).1⟩
  let cL : L := ⟨c,pCoreIn_le 2 L hc⟩
  have heL : l = rL * cL := Subtype.ext he.symm
  let ρ := doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes
  have hcfix (w : Additive D.sourceOrbit) : ρ cL w = w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change c * (w.toMul : G) * c⁻¹ = (w.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hcore hc w.toMul w.toMul.property).symm
  change f (ρ l v) = ρ l (f v)
  simp only [heL,map_mul,Module.End.mul_apply,hcfix]
  exact hf ⟨r,hr⟩ v

/-- The actual doubled A₇ orbit embeds in the center of the placed full two-core.
The native equivalence preserves the original residual and orbit inclusions. -/
theorem sourceOrbit_seven_mapped_core_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (K₀ : Subgroup G)
    (hr : oddActorResidual L A ≤ K₀) (hWK : D.sourceOrbit ≤ K₀)
    {Q : Type*} [Group Q] (m : K₀ ≃* Q) (M : Subgroup Q)
    (hrM : (m.toMonoidHom.comp (inclusion hr)).range ≤ M)
    (hwM : (m.toMonoidHom.comp (inclusion hWK)).range ≤ M)
    (hnR : M ≤ normalizer ((m.toMonoidHom.comp (inclusion hr)).range : Set Q))
    (hnW : M ≤ normalizer ((m.toMonoidHom.comp (inclusion hWK)).range : Set Q)) :
    256 ≤ Nat.card (center (pCore 2 M)) := by
  let : Finite Q := Finite.of_surjective m m.surjective
  let R := oddActorResidual L A
  let U := D.sourceOrbit
  let r := m.toMonoidHom.comp (inclusion hr)
  let w := m.toMonoidHom.comp (inclusion hWK)
  have hir : Function.Injective r := m.injective.comp (inclusion_injective hr)
  have hiw : Function.Injective w := m.injective.comp (inclusion_injective hWK)
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hRL : R ≤ L := (oddActorResidual_le L A).trans inf_le_left
  let ψ : R →* MulAut U := U.normalizerMonoidHom.comp
    (inclusion (hRL.trans D.sourceOrbit_component_normalizes))
  have hcore : pCore 2 R ≤ ψ.ker := by
    intro x hx
    change ψ x = 1
    ext y
    change (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (D.residual_core_centralizes h A hA ho (mem_map_of_mem R.subtype hx) y y.property).symm
  have hmark (x : R) (y : U) : w (ψ x y) = r x * w y * (r x)⁻¹ := by
    change m (inclusion hWK (ψ x y)) =
      m (inclusion hr x) * m (inclusion hWK y) * (m (inclusion hr x))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg m
    rfl
  have hc := mapped_core_centralizes_of_commutant M r w hir hiw hrM hnR hnW
    ψ hcore hmark (by
      intro f hf
      apply D.residual_centralizer_eq_one h hd σ hσ hmodel A hA ho f
      exact hf)
  have hp : IsPGroup 2 w.range :=
    (IsElementaryAbelian.isPGroup 2 U).of_surjective w.rangeRestrict w.rangeRestrict_surjective
  have hWP : w.range ≤ M.pCoreIn 2 := le_pCoreIn_of_normalizes hp hwM hnW
  have hZ : w.range ≤ (center (M.pCoreIn 2)).map (M.pCoreIn 2).subtype := by
    intro x hx
    refine ⟨⟨x,hWP hx⟩,mem_center_iff.mpr (fun p => ?_),rfl⟩
    exact Subtype.ext (hc p.property x hx).symm
  have hh := card_le_of_le hZ
  rw [card_map_of_injective (M.pCoreIn 2).subtype_injective] at hh
  let eP : pCore 2 M ≃* M.pCoreIn 2 :=
    (pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
  have hcard : Nat.card w.range = 256 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hiw).symm.toEquiv]
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_seven_dimension h hd σ hmodel] at he
    exact he
  exact hcard ▸ hh.trans_eq (Nat.card_congr (centerCongr eP).toEquiv).symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
