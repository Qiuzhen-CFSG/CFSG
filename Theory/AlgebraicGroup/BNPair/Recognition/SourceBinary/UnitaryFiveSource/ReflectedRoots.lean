module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.ReflectedPairing
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.NaturalRootKernel

/-!
# Compatible full unitary roots from reflection of the source pairing

Transport the entire pinned Hermitian root through the specified linear
reflection, keeping its center. Its natural noncentral coordinate and the
original first coordinate have precisely the same center kernel, and hence
differ by an additive equivalence. Reflecting the exact B–D commutator
reverses its arguments and forces this equivalence to be scalar times a
field involution. A moved crossed-linear root element selects the nontrivial
involution. One scalar change then gives the usual y·bar(x) crossing and
the conjugate-parameter Weyl action on the same crossed linear root.

The original-source application constructs the moved element using the
already identified Hermitian derived module. No whole-root parameter,
center, or exceptional small field is discarded.
Source: Fong--Seitz II (8C), (8.15)--(8.16), (8.21)--(8.23), pp.204,206--207.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure

private theorem same_kernel_equiv {H M N : Type*} [Group H] [Group M] [Group N]
    (f : H →* M) (g : H →* N) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hk : f.ker = g.ker) :
    ∃ e : M ≃* N, ∀ x, e (f x) = g x := by
  let a := QuotientGroup.liftEquiv f.ker hf rfl
  let b := QuotientGroup.liftEquiv f.ker hg hk
  refine ⟨a.symm.trans b,fun x => ?_⟩
  change b (a.symm (a (QuotientGroup.mk' f.ker x))) = g x
  rw [a.symm_apply_apply]
  rfl

private theorem center_comap_equiv {H M : Type*} [Group H] [Group M] (e : H ≃* M) :
    (center M).comap e.toMonoidHom = center H := by
  ext x
  change e x ∈ center M ↔ x ∈ center H
  simp only [mem_center_iff]
  constructor
  · intro hx y
    apply e.injective
    simpa only [map_mul] using hx (e y)
  · intro hx y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx z)

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (s : RootReflection Q split i)

/-- The whole opposite unitary root, including its center, is parametrized
by conjugating the pinned simple root with the specified source reflection. -/
def reflectedUnitaryChart {H : Type*} [Group H]
    (b : H ≃* simpleRoot Q split j) : H ≃* rootAt Q split j (Q.simple i) :=
  b.trans (({ (rightConjugateEquiv (simpleRoot Q split j) (s.val : X ⧸ Q.D)) with
    map_mul' := by intro x y; apply Subtype.ext; simp [mul_assoc] } :
      simpleRoot Q split j ≃* rightConjugate (simpleRoot Q split j) (s.val : X ⧸ Q.D)).trans
    (MulEquiv.subgroupCongr (rootAt_eq Q split j (Q.simple i) s.val s.class_eq).symm))

theorem reflectedUnitaryChart_apply {H : Type*} [Group H]
    (b : H ≃* simpleRoot Q split j) (p : H) :
    (reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D) =
      (s.val : X ⧸ Q.D)⁻¹ * (b p : X ⧸ Q.D) * s.val := by
  exact rightConjugateEquiv_apply (simpleRoot Q split j) (s.val : X ⧸ Q.D) (b p)

variable (hss : (s.val : X ⧸ Q.D) * s.val = 1)

/-- The linear reflection on the actual crossed linear root. -/
def crossedLinearReflection : MulAut (rootAt Q split i (Q.simple j)) where
  toFun x := ⟨(s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹,
    (SetLike.ext_iff.mp (cross_root_reflection_fixed Q split hm i j hij s.val s.class_eq) (x : X ⧸ Q.D)).mpr x.property⟩
  invFun x := ⟨(s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹,
    (SetLike.ext_iff.mp (cross_root_reflection_fixed Q split hm i j hij s.val s.class_eq) (x : X ⧸ Q.D)).mpr x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹)*(s.val : X ⧸ Q.D)⁻¹ = x
    rw [inv_eq_of_mul_eq_one_right hss]
    calc
      _ = ((s.val : X ⧸ Q.D)*s.val)*x*((s.val : X ⧸ Q.D)*s.val) := by group
      _ = _ := by rw [hss,one_mul,mul_one]
  right_inv x := by
    apply Subtype.ext
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹)*(s.val : X ⧸ Q.D)⁻¹ = x
    rw [inv_eq_of_mul_eq_one_right hss]
    calc
      _ = ((s.val : X ⧸ Q.D)*s.val)*x*((s.val : X ⧸ Q.D)*s.val) := by group
      _ = _ := by rw [hss,one_mul,mul_one]
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

private theorem reverse_crossing {Y : Type*} [Group Y] (b d c : Y)
    (hc : c*c=1) (hbc : Commute b c) (hdc : Commute d c)
    (h : b*d=d*c*b) : d*b=b*c*d := by
  calc
    d*b = d*c*(c*b) := by rw [mul_assoc,←mul_assoc c c b,hc,one_mul]
    _ = d*c*(b*c) := by rw [hbc.eq]
    _ = (d*c*b)*c := by group
    _ = (b*d)*c := by rw [h]
    _ = b*c*d := by rw [mul_assoc,hdc.eq,←mul_assoc]

variable {E : Type*} [Field E] [Finite E] [CharP E 2]
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (χ : rootAt Q split i (Q.simple j) ≃* Multiplicative E)
  (δ : rootAt Q split j (Q.simple i) →* Multiplicative E)
  (hδ : Function.Surjective δ)
  (hker : δ.ker = center (rootAt Q split j (Q.simple i)))

local notation "d" => reflectedUnitaryChart Q split i j s b
local notation "C" => (fun x : E => ((χ.symm (Multiplicative.ofAdd x)) : X ⧸ Q.D))

include hn hE hfixed hδ hker in
/-- The two full-root quotient coordinates differ by an additive equivalence;
the proof uses their exact full-center kernels. -/
theorem reflected_coordinate_equiv :
    ∃ f : E ≃+ E, ∀ p : hermitianUnipotentCoord J,
      f p.val.1 = (δ (d p)).toAdd := by
  have hk : (BinaryRootFrattini.firstCoordinate J).ker = center (hermitianUnipotentCoord J) := by
    apply le_antisymm (BinaryRootFrattini.first_kernel_central J)
    rw [binary_coord_center J hn hE hfixed]
    rintro p ⟨z,rfl⟩
    rfl
  have hd : Function.Surjective (δ.comp (d).toMonoidHom) := hδ.comp (d).surjective
  have he : (BinaryRootFrattini.firstCoordinate J).ker = (δ.comp (d).toMonoidHom).ker := by
    rw [←MonoidHom.comap_ker,hker,center_comap_equiv,hk]
  obtain ⟨f,hf⟩ := same_kernel_equiv (BinaryRootFrattini.firstCoordinate J)
    (δ.comp (d).toMonoidHom) (BinaryRootFrattini.firstCoordinate_surjective J hE hfixed) hd he
  refine ⟨AddEquiv.toMultiplicative.symm f,fun p => ?_⟩
  exact congrArg Multiplicative.toAdd (hf p)

variable (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (hcross : ∀ (p : hermitianUnipotentCoord J) (v : rootAt Q split j (Q.simple i)),
    (b p : X ⧸ Q.D)*v = v * (χ.symm (Multiplicative.ofAdd (p.val.1 * (δ v).toAdd)) : X ⧸ Q.D) * (b p : X ⧸ Q.D))

include hss hVi hVj hcross hE hfixed in
/-- Reflection reverses the same source commutator; these are equations on
whole unitary roots, before choosing common field labels. -/
theorem reflected_coordinate_pairing
    (f : E ≃+ E) (hf : ∀ p : hermitianUnipotentCoord J, f p.val.1 = (δ (d p)).toAdd) :
    let ψ := AddEquiv.toMultiplicative.symm
      ((χ.symm.trans (crossedLinearReflection Q split hm i j hij s hss)).trans χ)
    ∀ x y, ψ (x * f y) = y * f x := by
  dsimp only
  intro x y
  obtain ⟨p,hp⟩ := BinaryRootFrattini.firstCoordinate_surjective J hE hfixed (.ofAdd x)
  obtain ⟨q,hq⟩ := BinaryRootFrattini.firstCoordinate_surjective J hE hfixed (.ofAdd y)
  have hp' : p.val.1=x := congrArg Multiplicative.toAdd hp
  have hq' : q.val.1=y := congrArg Multiplicative.toAdd hq
  have hs_inv : (s.val : X ⧸ Q.D)⁻¹ = s.val := inv_eq_of_mul_eq_one_right hss
  have hdval (z : hermitianUnipotentCoord J) : (d z : X ⧸ Q.D) =
      (s.val : X ⧸ Q.D)*(b z : X ⧸ Q.D)*s.val := by rw [reflectedUnitaryChart_apply,hs_inv]
  have hdback (z : hermitianUnipotentCoord J) :
      (s.val : X ⧸ Q.D)*(d z : X ⧸ Q.D)*s.val = b z := by
    rw [hdval]
    calc
      _ = ((s.val : X ⧸ Q.D)*s.val)*(b z : X ⧸ Q.D)*((s.val : X ⧸ Q.D)*s.val) := by group
      _ = _ := by rw [hss,one_mul,mul_one]
  have hc1 : C (y*f x) * C (y*f x) = 1 := by
    change ((χ.symm (.ofAdd (y*f x)) * χ.symm (.ofAdd (y*f x))) : rootAt Q split i (Q.simple j)).val = 1
    rw [←map_mul]
    change (χ.symm (.ofAdd (y*f x + y*f x)) : X ⧸ Q.D) = 1
    rw [CharTwo.add_self_eq_zero]
    exact congrArg Subtype.val χ.symm.map_one
  have hbcomm : Commute (b q : X ⧸ Q.D) (C (y*f x)) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (adjacent_roots_commute Q split hm j i hij.symm hVj hVi) (b q).property)
      _ (χ.symm (.ofAdd (y*f x))).property).symm
  have hdcomm : Commute (d p : X ⧸ Q.D) (C (y*f x)) :=
    mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (middle_roots_commute Q split hm i j hij hVi hVj)
        (χ.symm (.ofAdd (y*f x))).property) _ (d p).property
  have hcqp := hcross q (d p)
  rw [←hf,hq',hp'] at hcqp
  have hreverse := reverse_crossing (b q : X ⧸ Q.D) (d p : X ⧸ Q.D)
    (C (y*f x)) hc1 hbcomm hdcomm hcqp
  have hcpq := hcross p (d q)
  rw [←hf,hp',hq'] at hcpq
  have hrefl := congrArg (MulAut.conj (s.val : X ⧸ Q.D)) hcpq
  simp only [map_mul,MulAut.conj_apply,hs_inv,←hdval,hdback] at hrefl
  rw [hreverse] at hrefl
  have he := mul_left_cancel (mul_right_cancel hrefl)
  apply Multiplicative.ofAdd.injective
  apply χ.symm.injective
  apply Subtype.val_injective
  change (χ.symm (χ (crossedLinearReflection Q split hm i j hij s hss
    (χ.symm (.ofAdd (x*f y))))) : X ⧸ Q.D) = C (y*f x)
  rw [χ.symm_apply_apply]
  change (s.val : X ⧸ Q.D)*C (x*f y)*(s.val : X ⧸ Q.D)⁻¹ = _
  rw [hs_inv]
  exact he.symm


include hm hij hss hn hE hfixed hδ hker hVi hVj hcross in
/-- The whole reflected unitary root has conjugate first coordinate. The same
scalar normalizes the crossed linear root and its specified reflection. -/
theorem reflected_unitary_labels
    (hmove : ∃ z : rootAt Q split i (Q.simple j),
      (s.val : X ⧸ Q.D)*z*(s.val : X ⧸ Q.D) ≠ z) :
    ∃ k : E, k ≠ 0 ∧
      (∀ p : hermitianUnipotentCoord J, (δ (d p)).toAdd = k * J.conj p.val.1) ∧
      (∀ a : E, (s.val : X ⧸ Q.D)*C (k*J.conj a)*s.val = C (k*a)) ∧
      ∀ p q : hermitianUnipotentCoord J,
        (b p : X ⧸ Q.D)*(d q : X ⧸ Q.D) =
          (d q : X ⧸ Q.D)*C (k*J.conj (q.val.1*J.conj p.val.1))*(b p : X ⧸ Q.D) := by
  obtain ⟨f,hf⟩ := reflected_coordinate_equiv Q split i j s J hn hE hfixed b δ hδ hker
  let ψ := AddEquiv.toMultiplicative.symm
    ((χ.symm.trans (crossedLinearReflection Q split hm i j hij s hss)).trans χ)
  have hp := reflected_coordinate_pairing Q split hm i j hij s hss J hE hfixed b χ δ hVi hVj hcross f hf
  have hψ : ψ ≠ AddEquiv.refl E := by
    intro he
    obtain ⟨z,hz⟩ := hmove
    have hz' := congrArg (fun e : E ≃+ E => e (χ z).toAdd) he
    have hh := congrArg Multiplicative.ofAdd hz'
    change χ (crossedLinearReflection Q split hm i j hij s hss (χ.symm (χ z))) = χ z at hh
    rw [χ.symm_apply_apply] at hh
    have hval := congrArg Subtype.val (χ.injective hh)
    change (s.val : X ⧸ Q.D)*z*(s.val : X ⧸ Q.D)⁻¹ = z at hval
    exact hz (by simpa only [inv_eq_of_mul_eq_one_right hss] using hval)
  have hτ : J.conj ≠ RingEquiv.refl E := by
    intro he
    let e : {x : E // J.conj x = x} ≃ E := {
      toFun := Subtype.val
      invFun := fun x => ⟨x,by rw [he]; rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hc := Nat.card_congr e
    rw [hfixed,hE] at hc
    have := Nat.one_lt_two_pow (show n ≠ 0 by omega)
    nlinarith
  obtain ⟨k,hk,hf',hp'⟩ := reflected_pairing_conjugation f ψ hp hψ J.conj J.conj_involutive hτ
  have hd (p : hermitianUnipotentCoord J) : (δ (d p)).toAdd = k * J.conj p.val.1 :=
    (hf p).symm.trans (hf' p.val.1)
  refine ⟨k,hk,hd,?_,?_⟩
  · intro a
    have hh := congrArg Multiplicative.ofAdd (hp' (J.conj a))
    change χ (crossedLinearReflection Q split hm i j hij s hss
      (χ.symm (.ofAdd (k*J.conj a)))) = .ofAdd (k*J.conj (J.conj a)) at hh
    rw [J.conj_involutive] at hh
    have hz := congrArg Subtype.val (χ.symm_apply_apply _ ▸ congrArg χ.symm hh)
    change (s.val : X ⧸ Q.D)*C (k*J.conj a)*(s.val : X ⧸ Q.D)⁻¹ = C (k*a) at hz
    simpa only [inv_eq_of_mul_eq_one_right hss] using hz
  · intro p q
    have hpoly : p.val.1 * (k*J.conj q.val.1) = k*J.conj (q.val.1*J.conj p.val.1) := by
      rw [map_mul,J.conj_involutive]
      ring
    simpa only [hd,hpoly] using hcross p (d q)

/-- The full pinned SU₃ upper root, with the original actor elements retained. -/
def pinnedUnitaryChart (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (θ : J.specialSubgroup ≃* rankOne Q split j)
    (hroot : ((rankOne Q split j).subtype.comp
      (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j) :
    hermitianUnipotentCoord J ≃* simpleRoot Q split j := by
  let b := (rankOne Q split j).subtype.comp
    (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))
  have hb : Function.Injective b := by
    intro p q hpq
    have he := θ.injective (Subtype.val_injective hpq)
    exact Subtype.ext (Prod.ext (congrArg (fun a : J.specialSubgroup => a.val.val 0 1) he)
      (congrArg (fun a : J.specialSubgroup => a.val.val 0 2) he))
  exact (MonoidHom.ofInjective hb).trans (MulEquiv.subgroupCongr hroot)

omit [Finite E] [CharP E 2] in
theorem pinnedUnitaryChart_apply (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (θ : J.specialSubgroup ≃* rankOne Q split j)
    (hroot : ((rankOne Q split j).subtype.comp
      (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j)
    (p : hermitianUnipotentCoord J) :
    (pinnedUnitaryChart Q split j J hJ θ hroot p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p) := rfl

/-- Normalize the faithful crossed linear chart by the scalar forced by the
whole-root pairing and the actual Hermitian involution. -/
def normalizedCrossChart (k : E) (hk : k ≠ 0) :
    Multiplicative E ≃* rootAt Q split i (Q.simple j) :=
  (AddEquiv.toMultiplicative (J.conj.toAddEquiv.trans
    ({ Equiv.mulLeft₀ k hk with map_add' := mul_add k } : E ≃+ E))).trans χ.symm

omit [Finite E] [CharP E 2] in
theorem normalizedCrossChart_apply (k : E) (hk : k ≠ 0) (a : E) :
    normalizedCrossChart Q split i j J χ k hk (.ofAdd a) =
      χ.symm (.ofAdd (k*J.conj a)) := rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
