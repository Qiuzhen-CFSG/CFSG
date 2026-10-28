module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.ScalarFamilies.Second
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.ScalarFamilies.FirstKernel


/-!
# The full first Cartan scalar family

The independently constructed terminal generator acts by λ² on W₁ and
λ on W₂. Combine its powers with actors in X intersect L₂ to cancel the
scalar on W₂. Since squaring is bijective over the finite field of
characteristic two, every nonzero scalar occurs on W₁. The literal
quotient-kernel calculation puts these actors in X₁.

The conjugation representation on V passes this scalar to [W₂,W₁].
Agreement on P intersect V identifies it with the inherited scalar on
the actual W₃ = [W₁,W₂] inside P. This gives the full (a,1,a) family;
no terminal contradiction is used to construct its actors.

The assembly in ScalarFamilies discharges the remaining complement and
terminal premises. The parent qt-d-1222-shadow-linear-geometry retains
discharge of the preceding common-core geometry and independent markings.

Source: Aschbacher--Smith, 11.3.8--9 and Proposition 11.3.2, printed
pp.774--775.
-/

open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies

private theorem scalar_mul {G F : Type*} [Group G] [Field F]
    (W : Subgroup G) [IsMulCommutative W] [Module F (Additive W)]
    {x y : G} {a b : F} (hx : ScalarConjugation W x a) (hy : ScalarConjugation W y b) :
    ScalarConjugation W (x*y) (a*b) := by
  intro w
  rw [map_mul,MulAut.mul_apply,hy,hx,smul_smul]

private theorem scalar_pow {G F : Type*} [Group G] [Field F]
    (W : Subgroup G) [IsMulCommutative W] [Module F (Additive W)]
    {x : G} {a : F} (hx : ScalarConjugation W x a) (n : ℕ) :
    ScalarConjugation W (x^n) (a^n) := by
  induction n with
  | zero => intro w; simp
  | succ n ih => simpa only [pow_succ] using scalar_mul W ih hx

private theorem primitive_square_powers {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : F) (ha : a ≠ 0) (ho : orderOf a = Nat.card F-1) (r : F) (hr : r ≠ 0) :
    ∃ n : ℕ, (a^n)^2 = r := by
  obtain ⟨s,hs⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) r
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hr hs.symm
  let u := Units.mk0 a ha
  have ht : zpowers u = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (zpowers u)).mp
    rw [Nat.card_zpowers,←orderOf_units,Nat.card_units]
    exact ho
  have hm : Units.mk0 s hs0 ∈ zpowers u := ht ▸ mem_top _
  obtain ⟨n,hn⟩ := (isOfFinOrder_of_finite u).mem_powers_iff_mem_zpowers.mpr hm
  have hn' : a^n = s := congrArg (fun v : Fˣ => (v : F)) hn
  exact ⟨n,hn' ▸ hs⟩

/-- In the first family, the scalar on V passes to the same commutator field
inside P, using the constructed agreement on P intersect V. -/
theorem first_scalar_on_commutator {G F : Type*} [Group G] [Field F]
    {P V L Y : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]
    [Module F (Additive P)] [Module F (Additive V)]
    (hcommon : ∀ (a : F) (b : Additive (P ⊓ V : Subgroup G)),
      ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
      ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))
    (τ : Representation F L (Additive V))
    (hτ : ∀ (l : L) (v : Additive V),
      ((τ l v).toMul : G) = MulAut.conj (l : G) (v.toMul : G))
    (σ : Representation F Y (Additive P))
    (hσ : ∀ (y : Y) (p : Additive P),
      ((σ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G))
    (U₁ : Submodule F (Additive V)) (U₂ : Submodule F (Additive P))
    (h₁ : ambientSubgroup U₁ ≤ Y) (h₂ : ambientSubgroup U₂ ≤ L)
    (x : L) (a : F) :
    let C := commutatorFieldSpace σ h₁ U₂
    let := subgroupFieldModule U₁ rfl
    let := subgroupFieldModule U₂ rfl
    let := subgroupFieldModule C rfl
    ScalarConjugation (ambientSubgroup U₁) (x : G) a →
    ScalarConjugation (ambientSubgroup U₂) (x : G) (1 : F) →
    ScalarConjugation (ambientSubgroup C) (x : G) a := by
  let C := commutatorFieldSpace σ h₁ U₂
  let C' := commutatorFieldSpace τ h₂ U₁
  let := subgroupFieldModule U₁ rfl
  let := subgroupFieldModule U₂ rfl
  let := subgroupFieldModule C rfl
  dsimp only
  intro hx₁ hx₂
  have he : ambientSubgroup C' = ambientSubgroup C := by
    rw [ambient_commutatorFieldSpace τ hτ,ambient_commutatorFieldSpace σ hσ,commutator_comm]
  have hCV : ambientSubgroup C ≤ V := he ▸ map_subtype_le _
  have hc (w : ambientSubgroup U₂) : Commute (x : G) (w : G) := by
    have hh := hx₂ (Additive.ofMul w)
    apply (commute_iff_eq _ _).mpr
    simpa only [one_smul,MulAut.conj_apply,mul_inv_eq_iff_eq_mul,toMul_ofMul] using hh
  have hu : ∀ u ∈ U₁, τ x u = a • u := by
    intro u hu
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hτ]
    exact (scalarConjugation_iff U₁ rfl _ _).mp hx₁ u hu
  intro c
  let v : Additive V := (inclusion hCV).toAdditive c
  have hv : v ∈ C' := (mem_ambientSubgroup C' _).mp (he.symm ▸ c.toMul.property)
  have hs := scalar_on_commutatorFieldSpace τ h₂ U₁ x a hc hu v hv
  rw [subgroupFieldModule_smul_common hcommon C rfl hCV]
  exact (hτ x v).symm.trans (congrArg (fun z : Additive V => (z.toMul : G)) hs)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
open TerminalWeights
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) {P I K X : Subgroup G}
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (o : CommonCore.OrthogonalMarking (f.Li 1 ⊔ I) P K (f.Li 1) E)
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)
    (hodd : Odd S.field.degree) (hPK : P = K.pCoreIn 2)
    (hPT : P ≤ T) (hTY : (T : Subgroup G) ≤ f.Li 1 ⊔ I)
    (hTL : (T : Subgroup G) ≤ L)

open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open MarkedSections.RadicalGeometry

include hX hXY hodd hPK hPT hTY hTL in
/-- Every nonzero scalar occurs in the literal first Cartan factor with
weights (a,1,a) on the actual complements and their commutator. -/
theorem source_first_scalar_family :
    let := originalModule D (.sl3 m) hfixed
    let s := orderedSection o
    let := s.moduleStructure
    let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
    let := d.compatibleModule hcard
    let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
    ∀ (W₁ : Submodule S.field.Carrier (Additive V))
      (W₂ : Submodule S.field.Carrier (Additive P)),
      IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ →
      Module.finrank S.field.Carrier W₂ = 1 →
      Disjoint (P ⊓ f.Ri 0) (ambientSubgroup W₂) →
      X ≤ normalizer (ambientSubgroup W₁ : Set G) →
      X ≤ normalizer (ambientSubgroup W₂ : Set G) →
    let C := commutatorFieldSpace σ
      ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
    let := subgroupFieldModule W₁ rfl
    let := subgroupFieldModule W₂ rfl
    let := subgroupFieldModule C rfl
    ∀ r : S.field.Carrier, r ≠ 0 →
      ∃ x ∈ X ⊓ coreQuotientCentralizer (f.Li 0),
      ScalarConjugation (ambientSubgroup W₁) x r ∧
      ScalarConjugation (ambientSubgroup W₂) x (1 : S.field.Carrier) ∧
      ScalarConjugation (ambientSubgroup C) x r := by
  let := originalModule D (.sl3 m) hfixed
  let s := orderedSection o
  let := s.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
  dsimp only
  intro W₁ W₂ hc₁ hd₂ hdis hn₁ hn₂
  let C := commutatorFieldSpace σ
    ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
  let := subgroupFieldModule W₁ rfl
  let := subgroupFieldModule W₂ rfl
  let := subgroupFieldModule C rfl
  obtain ⟨y,lam,Q,_,hlam,ho,hcompl,hW₂,_,hU,hQ,_,_,_,hUambient,_⟩ :=
    source_plane_spectrum D S m f hfixed E o hcard hP hcore hPV hVI hX hXY
      hodd hPK hPT hTY hTL W₂ hd₂ hdis hn₂
  let U := SeparatePlaneActions.fixedPlane (V := V) σ
  obtain ⟨hy₁,hy₂,_⟩ := source_weights_of_planes D S m f hfixed E s hcard
    hP hcore hPV hVI hX hXY W₁ W₂ U Q hc₁ hcompl hW₂
    hUambient.le hn₁ y lam⁻¹ lam hlam hU hQ
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show W₂ ≠ ⊥ from by
    intro he
    rw [he,finrank_bot] at hd₂
    omega)
  have hwR : (w.toMul : G) ∉ f.Ri 0 := by
    intro hh
    have hh' : (w.toMul : G) ∈ (P ⊓ f.Ri 0) ⊓ ambientSubgroup W₂ :=
      ⟨⟨w.toMul.property,hh⟩,(mem_ambientSubgroup W₂ _).mpr hw⟩
    have hzero : (w.toMul : G) = 1 := hdis.le_bot hh'
    apply hw0
    exact Additive.toMul.injective (Subtype.ext hzero)
  intro r hr
  obtain ⟨n,hn⟩ := primitive_square_powers lam hlam (ho.trans (by rw [S.field.card_eq])) r hr
  obtain ⟨z,hz,hz₁,hz₂,_⟩ := source_second_scalar_family D S m f hfixed E o hcard hP hcore hPV hVI
    hX hXY hPT hTY hTL W₁ W₂ hc₁ hd₂ hn₁ hn₂ (lam^n)⁻¹ (inv_ne_zero (pow_ne_zero _ hlam))
  let x : G := (y : G)^n * z
  have hx : x ∈ X := X.mul_mem (X.pow_mem y.property.1 _) hz.1
  have hx₁ : ScalarConjugation (ambientSubgroup W₁) x r := by
    have hh := scalar_mul _ (scalar_pow _ hy₁ n) hz₁
    have hn2 : (lam^2)^n = r := by rw [←pow_mul, Nat.mul_comm 2 n, pow_mul,hn]
    simpa only [mul_one,hn2] using hh
  have hx₂ : ScalarConjugation (ambientSubgroup W₂) x (1 : S.field.Carrier) := by
    have hh := scalar_mul _ (scalar_pow _ hy₂ n) hz₂
    simpa only [mul_inv_cancel₀ (pow_ne_zero n hlam)] using hh
  have hcomm (v : ambientSubgroup W₂) : Commute x (v : G) := by
    have hh := hx₂ (Additive.ofMul v)
    apply (commute_iff_eq _ _).mpr
    simpa only [one_smul,MulAut.conj_apply,mul_inv_eq_iff_eq_mul,toMul_ofMul] using hh
  have hxkernel := first_kernel_of_fixed_element D S m f hX hP hTL ⟨x,hx⟩ w.toMul hwR
    (hcomm ⟨w.toMul,(mem_ambientSubgroup W₂ _).mpr hw⟩)
  refine ⟨x,⟨hx,hxkernel⟩,hx₁,hx₂,?_⟩
  have hPL : P ≤ L := hP ▸ (pCoreIn_le 2 (f.Li 1)).trans
    ((localResidual_le _).trans inf_le_left)
  exact first_scalar_on_commutator (d.common_smul hcard)
    (MarkedSections.originalRepresentation D (.sl3 m) hfixed)
    (MarkedSections.originalRepresentation_conj D (.sl3 m) hfixed) σ s.action_conj
    W₁ W₂ _ ((map_subtype_le _).trans hPL)
    ⟨x,(hX.1.trans inf_le_left) hx⟩ r hx₁ hx₂
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
