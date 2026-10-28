module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvariantCubicGeneration
public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# Source parabolics above the binary derived G₂ quotient

Both actual derived G₂ parabolics have a two-residual element whose sixth
power is nonidentity. A product of conjugate cubic elements gives the
witness; only its few products are checked against the existing realized
96-row tables. The first witness is transported through the marked
first-parabolic equivalence, and the second marking is definitional.

Above a two-core quotient, the two parabolic preimages contain the original
Sylow subgroup, have characteristic two, and generate the whole group.
Every automorphism preserving that Sylow fixes both preimages. Their actual
surjections to the marked model parabolics retain two-group kernels.

Source: Aschbacher--Smith 15.1.22(*), (2), printed pp.1098--1100, and
F.1.12(I)(8), printed p.263. The root-word tables and their actual realization
are the licensed ATLAS port; see LICENSES/ATLAS.txt and the imported
ExceptionalLocalQuotients module. No new whole-group enumeration is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryParabolicPair
open ExceptionalLocalQuotients
open Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
open Atlas.G2.LieAutomorphismExtensions
private def rowPow (T : WordTable) (i : Fin 96) : ℕ → Fin 96
  | 0 => 0
  | n+1 => T.mul (rowPow T i n) i
private theorem rowPow_eq {X : Type*} [Group X] {T : WordTable}
    (E : T.Realization X) (i : Fin 96) (n : ℕ) :
    E.equiv (rowPow T i n) = E.equiv i ^ n := by
  induction n with
  | zero => simpa only [rowPow, pow_zero] using E.one_eq
  | succ n ih => rw [rowPow, E.mul_eq, ih, pow_succ]
private theorem witness {X : Type*} [Group X] {T : WordTable}
    (E : T.Realization X) (j : Fin 96)
    (hinv : T.mul 1 j = 0) (hcube : rowPow T 2 3 = 0)
    (hpow : rowPow T (T.mul 2 (T.mul (T.mul 1 2) j)) 6 ≠ 0) :
    ∃ y ∈ pResidual 2 X, y^6 ≠ 1 := by
  have hinv' : E.equiv j = (E.equiv 1)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [←E.mul_eq, hinv, E.one_eq]
  have hb : E.equiv 2 ∈ pResidual 2 X := by
    apply mem_pResidual_of_orderOf_coprime
    apply (by decide : Nat.Coprime 2 3).of_dvd_right
    apply orderOf_dvd_of_pow_eq_one
    rw [←rowPow_eq, hcube, E.one_eq]
  let w := T.mul 2 (T.mul (T.mul 1 2) j)
  refine ⟨E.equiv w, ?_, ?_⟩
  · change E.equiv (T.mul 2 (T.mul (T.mul 1 2) j)) ∈ _
    rw [E.mul_eq, E.mul_eq, E.mul_eq, hinv']
    exact (pResidual 2 X).mul_mem hb ((inferInstance : (pResidual 2 X).Normal).conj_mem _ hb _)
  · intro hh
    apply hpow
    apply E.equiv.injective
    rw [rowPow_eq, hh, E.one_eq]
private theorem left_witness : ∃ y ∈ pResidual 2 BinaryLeft, y^6 ≠ 1 :=
  witness binaryConcreteRealization.left 53 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
private theorem right_witness : ∃ y ∈ pResidual 2 BinaryRight, y^6 ≠ 1 :=
  witness binaryConcreteRealization.right 68 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- A concrete product of conjugate cubics in the first derived parabolic
has nonidentity sixth power, even after restriction to its two-residual. -/
theorem derivedFirst_residual_not_exponent_six :
    ∃ y ∈ pResidual 2 derivedFirst, y^6 ≠ 1 := by
  obtain ⟨x,hx,he⟩ := left_witness
  refine ⟨firstMarkedEquiv x,
    map_pResidual_le 2 firstMarkedEquiv.toMonoidHom
      (mem_map_of_mem firstMarkedEquiv.toMonoidHom hx),?_⟩
  intro hh
  apply he
  apply firstMarkedEquiv.injective
  rw [map_pow,hh,map_one]

/-- The corresponding concrete witness in the second derived parabolic. -/
theorem derivedSecond_residual_not_exponent_six :
    ∃ y ∈ pResidual 2 derivedSecond, y^6 ≠ 1 := right_witness

private theorem pair_generate : derivedFirst ⊔ derivedSecond = ⊤ := by
  apply map_injective (f := DerivedModel.subtype) DerivedModel.subtype_injective
  rw [Subgroup.map_sup, derivedFirst_map_subtype, derivedSecond_map_subtype,
    ←MonoidHom.range_eq_map, DerivedModel.range_subtype]
  have h := DerivedParabolicGeneration.binary_restricted_pair_generate
  rw [LieParabolicSetup.parabolic₁_binary] at h
  exact h
private theorem pair_invariant (a : MulAut DerivedModel)
    (ha : (derivedSylow : Subgroup DerivedModel).map a.toMonoidHom = derivedSylow) :
    derivedFirst.map a.toMonoidHom = derivedFirst ∧
      derivedSecond.map a.toMonoidHom = derivedSecond := by
  rw [derivedSylow_eq] at ha
  have hh := SylowParabolicInvariance.restricted_parabolics_invariant a ha
  rw [LieParabolicSetup.parabolic₁_binary] at hh
  exact hh
private theorem map_comap_equivariant {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (a : MulAut X) (b : MulAut Y)
    (he : ∀ x, q (a x) = b (q x)) (P : Subgroup Y)
    (hP : P.map b.toMonoidHom = P) :
    (P.comap q).map a.toMonoidHom = P.comap q := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change q (a x) ∈ P
    rw [he]
    exact hP ▸ mem_map_of_mem b.toMonoidHom hx
  · intro x hx
    refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
    change q (a.symm x) ∈ P
    have hh : b (q (a.symm x)) ∈ P := by rw [←he,a.apply_symm_apply]; exact hx
    rw [←hP,mem_map_equiv] at hh
    simpa only [b.symm_apply_apply] using hh

private theorem lift_pair {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (S₀ : Sylow 2 Y) (P R : Subgroup Y)
    (hgen : P ⊔ R = ⊤) (hSP : (S₀ : Subgroup Y) ≤ P) (hSR : (S₀ : Subgroup Y) ≤ R)
    (hinv : ∀ a : MulAut Y, (S₀ : Subgroup Y).map a.toMonoidHom = S₀ →
      P.map a.toMonoidHom = P ∧ R.map a.toMonoidHom = R)
    (hf : generalizedFitting X = pCore 2 X)
    (e : (X ⧸ pCore 2 X) ≃* Y) (S : Sylow 2 X) :
    ∃ C E : Subgroup X, C ⊔ E = ⊤ ∧
      (S : Subgroup X) ≤ C ∧ (S : Subgroup X) ≤ E ∧
      generalizedFitting C = pCore 2 C ∧ generalizedFitting E = pCore 2 E ∧
      (∃ f : C →* P, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∃ f : E →* R, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∀ a : MulAut X, (S : Subgroup X).map a.toMonoidHom = S →
        C.map a.toMonoidHom = C ∧ E.map a.toMonoidHom = E) := by
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let U := S.mapSurjective (f := q₀) hq₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Y U S₀
  let t := e.trans (MulAut.conj g)
  let q := t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := t.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ t.injective,QuotientGroup.ker_mk']
  have hS : (S : Subgroup X).map q = S₀ := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup X).map q₀).map (MulAut.conj g).toMonoidHom = _ at hh
    rw [map_map] at hh
    exact hh
  let C := P.comap q
  let E := R.comap q
  have hSC : (S : Subgroup X) ≤ C := (map_le_iff_le_comap).mp (hS ▸ hSP)
  have hSE : (S : Subgroup X) ≤ E := (map_le_iff_le_comap).mp (hS ▸ hSR)
  have hfit (D : Subgroup X) (hSD : (S : Subgroup X) ≤ D) :
      generalizedFitting D = pCore 2 D :=
    generalizedFitting_eq_pCore_of_normalized_by_pCore D hf
      ((pCore_isPGroup.le_sylow_of_normal S).trans (hSD.trans D.le_normalizer))
  have cover (P : Subgroup Y) :
      ∃ f : P.comap q →* P, Function.Surjective f ∧ IsPGroup 2 f.ker := by
    let f : P.comap q →* P := (q.comp (P.comap q).subtype).codRestrict P (fun x => x.property)
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨x,hx⟩ := hq y
      exact ⟨⟨x,show q x ∈ P from hx.symm ▸ y.property⟩,Subtype.ext hx⟩
    refine ⟨f,hfs,?_⟩
    have he : f.ker = q.ker.subgroupOf (P.comap q) := by
      ext x
      change (⟨q x,x.property⟩ : P) = 1 ↔ q x = 1
      exact Subtype.ext_iff
    rw [he,hk]
    exact pCore_isPGroup.comap_subtype
  refine ⟨C,E,?_,hSC,hSE,hfit C hSC,hfit E hSE,cover _,cover _,?_⟩
  · change P.comap q ⊔ R.comap q = ⊤
    rw [comap_sup_eq _ _ _ hq,hgen,comap_top]
  · intro a ha
    let b := MulAut.congr t (quotientAut (pCore 2 X) a)
    have he (x : X) : q (a x) = b (q x) := by
      change t (QuotientGroup.mk' (pCore 2 X) (a x)) =
        t (quotientAut (pCore 2 X) a (t.symm (t (QuotientGroup.mk' (pCore 2 X) x))))
      rw [t.symm_apply_apply,quotientAut_apply_mk]
    have hUb : (S₀ : Subgroup Y).map b.toMonoidHom = S₀ := by
      rw [←hS]
      have hhom : b.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext (fun x => (he x).symm)
      rw [map_map,hhom,←map_map,ha]
    exact ⟨map_comap_equivariant q a b he _ (hinv b hUb).1,
      map_comap_equivariant q a b he _ (hinv b hUb).2⟩

/-- The two marked parabolics lift to a generating, Sylow-invariant pair
through the original two-core, with the actual model quotient maps. -/
theorem exists_core_parabolic_pair {X : Type*} [Group X] [Finite X]
    (hf : generalizedFitting X = pCore 2 X)
    (e : (X ⧸ pCore 2 X) ≃* DerivedModel) (S : Sylow 2 X) :
    ∃ C E : Subgroup X, C ⊔ E = ⊤ ∧
      (S : Subgroup X) ≤ C ∧ (S : Subgroup X) ≤ E ∧
      generalizedFitting C = pCore 2 C ∧ generalizedFitting E = pCore 2 E ∧
      (∃ f : C →* derivedFirst, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∃ f : E →* derivedSecond, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∀ a : MulAut X, (S : Subgroup X).map a.toMonoidHom = S →
        C.map a.toMonoidHom = C ∧ E.map a.toMonoidHom = E) :=
  lift_pair derivedSylow derivedFirst derivedSecond pair_generate
    derivedSylow_le_first derivedSylow_le_second pair_invariant hf e S

end Atlas.G2.BinaryParabolicPair
