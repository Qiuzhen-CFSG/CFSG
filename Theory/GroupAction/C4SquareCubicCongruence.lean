module

public import Theory.GroupAction.C4SquareActionDichotomySetup
public import Theory.GroupAction.C4SquareFixedKernel

/-!
# The cubic moved plane in the C₄-square congruence kernel

The automorphisms fixing all square-one elements form an elementary abelian
congruence kernel. Conjugation by a cubic automorphism acts on this kernel.
We construct the moved plane as the image of its displacement homomorphism.
A binary coordinate calculation shows that a nonidentity displacement fixes
only square-one elements. Evaluation at a primitive point bounds the image
by four; its nontrivial fixed-free cubic action forces equality. The kernel
is the centralizer, so the given centralizer bound gives index one or two.

Source: MacWilliams, Trans. AMS 150 (1970), printed p.380, congruence-kernel
discussion and (xxi),
`refs/original/n-group-global/odd-core-rank-two-source/macwilliams-1970-ams-wayback.pdf`.
-/

set_option synthInstance.maxSize 4096

open scoped IsMulCommutative
namespace C4SquareExtension
open ActionDichotomy

-- Coordinates for b f b⁻¹ f, using b⁻¹=b² and f⁻¹=f.
private def disp (p : OuterCode) (m : Code) (x : Model) : Model :=
  outerAct p (congruenceAct m (outerAct p (outerAct p (congruenceAct m x))))

private def Cubic (p : OuterCode) : Prop :=
  (∀ x : Model, outerAct p (outerAct p (outerAct p x)) = x) ∧
  ¬ (∀ x : Model, outerAct p x = x)

private instance (p : OuterCode) : Decidable (Cubic p) := by
  unfold Cubic
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem displacement_fixed : ∀ p : OuterCode, Cubic p → ∀ m : Code,
    (∃ x : Model, disp p m x ≠ x) → ∀ x : Model,
    disp p m x = x → x ^ 2 = 1 := by decide +kernel

private theorem fixed_displacement (b f : MulAut Model)
    (hb3 : b ^ 3 = 1) (hbne : b ≠ 1)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x)
    (hne : b * f * b⁻¹ * f⁻¹ ≠ 1)
    (x : Model) (hx : (b * f * b⁻¹ * f⁻¹) x = x) : x ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := exists_congruenceAut f hf
  have hbI : b⁻¹ = b * b := by
    calc
      b⁻¹ = b⁻¹ * b ^ 3 := by rw [hb3]; simp
      _ = b * b := by simp only [pow_succ, pow_zero]; group
  let p : OuterCode := (b e₁, b e₂)
  have heval (y : Model) :
      (b * congruenceAut m * b⁻¹ * (congruenceAut m)⁻¹) y = disp p m y := by
    change b (congruenceAct m (b⁻¹ (congruenceAct m y))) = _
    rw [hbI]
    change b (congruenceAct m (b (b (congruenceAct m y)))) = _
    dsimp [disp, p]
    simp only [← aut_eq_outerAct]
  have hc : Cubic p := by
    constructor
    · intro y
      change outerAct (b e₁, b e₂) (outerAct (b e₁, b e₂) (outerAct (b e₁, b e₂) y)) = y
      simp only [← aut_eq_outerAct]
      have hh := congrArg (fun g : MulAut Model => g y) hb3
      simpa [pow_succ, pow_two, MulAut.mul_apply] using hh
    · intro hh
      apply hbne
      apply MulEquiv.ext
      intro y
      exact (aut_eq_outerAct b y).trans (hh y)
  have hn : ∃ y : Model, disp p m y ≠ y := by
    by_contra! hn
    apply hne
    apply MulEquiv.ext
    intro y
    exact (heval y).trans (hn y)
  exact displacement_fixed p hc m hn x ((heval x).symm.trans hx)

private theorem abstract_plane {A : Type*} [CommGroup A] [Finite A]
    (c : A →* A) (hc3 : ∀ x, c (c (c x)) = x)
    (h2 : ∀ x : A, x ^ 2 = 1)
    (hn : ∃ x, c x ≠ x)
    (hbound : Nat.card (c * (MonoidHom.id A)⁻¹).range ≤ 4)
    (hker : Nat.card (c * (MonoidHom.id A)⁻¹).ker ≤ 2) :
    let d := c * (MonoidHom.id A)⁻¹
    Nat.card d.range = 4 ∧ (d.range.index = 1 ∨ d.range.index = 2) ∧
      (∀ x ∈ d.range, c x ∈ d.range) ∧
      (∀ x ∈ d.range, c x = x → x = 1) := by
  classical
  let d := c * (MonoidHom.id A)⁻¹
  have hd (x : A) : d x = c x * x⁻¹ := rfl
  have hcd (x : A) : c (d x) = d (c x) := by simp [hd]
  have hnorm (x : A) (hx : x ∈ d.range) : c x ∈ d.range := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨c y, (hcd y).symm⟩
  have hfree (x : A) (hx : x ∈ d.range) (hc : c x = x) : x = 1 := by
    obtain ⟨y, rfl⟩ := hx
    have ht : d y * c (d y) * c (c (d y)) = 1 := by
      simp only [hd, map_mul, map_inv, hc3]
      simp [mul_comm, mul_left_comm, mul_assoc]
    rw [hc, hc, ← pow_two, h2, one_mul] at ht
    exact ht
  obtain ⟨x, hx⟩ := hn
  let u : d.range := ⟨d x, ⟨x, rfl⟩⟩
  have hu : u ≠ 1 := by
    intro h
    apply hx
    have hh : c x * x⁻¹ = 1 := congrArg Subtype.val h
    exact mul_inv_eq_one.mp hh
  have ho : orderOf u = 2 := orderOf_eq_prime (Subtype.ext (h2 _)) hu
  have hdvd : 2 ∣ Nat.card d.range := ho ▸ orderOf_dvd_natCard u
  have hpos : 0 < Nat.card d.range := Nat.card_pos
  have hnot2 : Nat.card d.range ≠ 2 := by
    intro htwo
    obtain ⟨v, hv, huniq⟩ := (Nat.card_eq_two_iff' (1 : d.range)).mp htwo
    let w : d.range := ⟨c u, hnorm _ u.property⟩
    have hw : w ≠ 1 := by
      intro h
      apply hu
      apply Subtype.ext
      have hh : c (u : A) = 1 := congrArg Subtype.val h
      calc
        (u : A) = c (c (c (u : A))) := (hc3 _).symm
        _ = 1 := by rw [hh]; simp
    have hfix : c (u : A) = u := congrArg Subtype.val ((huniq w hw).trans (huniq u hu).symm)
    exact hu (Subtype.ext (hfree _ u.property hfix))
  change Nat.card d.range ≤ 4 at hbound
  change Nat.card d.ker ≤ 2 at hker
  have hcard : Nat.card d.range = 4 := by omega
  refine ⟨hcard, ?_, hnorm, hfree⟩
  have hi : d.range.index = Nat.card d.ker := Subgroup.index_range
  have hp : 0 < Nat.card d.ker := Nat.card_pos
  rw [hi]
  omega

private theorem model_plane
    {H : Subgroup (MulAut Model)} {b : MulAut Model}
    (hb3 : b ^ 3 = 1) (hbne : b ≠ 1)
    (hfix : ∀ f ∈ H, ∀ x : Model, x ^ 2 = 1 → f x = x)
    (hnorm : ∀ f ∈ H, b * f * b⁻¹ ∈ H)
    (hcent : Nat.card (H ⊓ Subgroup.centralizer ({b} : Set (MulAut Model)) :
      Subgroup (MulAut Model)) ≤ 2)
    (hncomm : ¬ ∀ f ∈ H, Commute f b) :
    ∃ V : Subgroup (MulAut Model), V ≤ H ∧ Nat.card V = 4 ∧
      (V.relIndex H = 1 ∨ V.relIndex H = 2) ∧
      (∀ f ∈ V, b * f * b⁻¹ ∈ V) ∧
      (∀ f ∈ V, b * f * b⁻¹ = f → f = 1) ∧
      (∀ f ∈ V, f ≠ 1 → ∀ x : Model, f x = x → x ^ 2 = 1) := by
  classical
  let : IsMulCommutative H := IsMulCommutative.of_comm fun f g =>
    Subtype.ext (commute_of_fix_square_one f g (hfix f f.property) (hfix g g.property)).eq
  let c : H →* H := {
    toFun := fun f => ⟨b * f * b⁻¹, hnorm f f.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro f g
      apply Subtype.ext
      change b * ((f : MulAut Model) * g) * b⁻¹ =
        (b * f * b⁻¹) * (b * g * b⁻¹)
      group }
  have hc (f : H) : (c f : MulAut Model) = b * f * b⁻¹ := rfl
  have hc3 (f : H) : c (c (c f)) = f := by
    apply Subtype.ext
    simp only [hc]
    calc
      b * (b * (b * f * b⁻¹) * b⁻¹) * b⁻¹ = b ^ 3 * f * (b ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero]
        group
      _ = f := by rw [hb3]; simp
  have h2 (f : H) : f ^ 2 = 1 :=
    Subtype.ext (square_eq_one_of_fix_square_one f (hfix f f.property))
  have hn : ∃ f : H, c f ≠ f := by
    by_contra! hn
    apply hncomm
    intro f hf
    have hh := congrArg Subtype.val (hn ⟨f, hf⟩)
    change b * f * b⁻¹ = f at hh
    exact ((mul_inv_eq_iff_eq_mul.mp hh) : b * f = f * b).symm
  let d := c * (MonoidHom.id H)⁻¹
  have hd (f : H) : (d f : MulAut Model) = b * f * b⁻¹ * (f : MulAut Model)⁻¹ := rfl
  have hfixed (f : d.range) (hne : f ≠ 1) (x : Model)
      (hx : (f : H).val x = x) : x ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := f.property
    have hne' : b * g * b⁻¹ * g⁻¹ ≠ 1 := by
      intro hh
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      rw [← hg]
      exact hh
    apply fixed_displacement b g hb3 hbne (hfix g g.property) hne' x
    rw [← hd, hg]
    exact hx
  let j : d.range → {x : Model // x ^ 2 = e₁ ^ 2} := fun f =>
    ⟨(f : H).val e₁, by
      rw [← map_pow]
      exact hfix (f : H) (f : H).property _ (by decide)⟩
  have hj : Function.Injective j := by
    intro f g h
    have hh : (f : H).val e₁ = (g : H).val e₁ := congrArg Subtype.val h
    have hfg : f⁻¹ * g = 1 := by
      by_contra hne
      have hs := hfixed (f⁻¹ * g) hne e₁ (by
        change (f : H).val.symm ((g : H).val e₁) = e₁
        rw [← hh]
        exact (f : H).val.symm_apply_apply e₁)
      exact (by decide : e₁ ^ 2 ≠ 1) hs
    exact inv_mul_eq_one.mp hfg
  have hbound : Nat.card d.range ≤ 4 := by
    have ht : Nat.card {x : Model // x ^ 2 = e₁ ^ 2} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    exact (Nat.card_le_card_of_injective j hj).trans_eq ht
  have hker : Nat.card d.ker ≤ 2 := by
    let k : d.ker → ↥(H ⊓ Subgroup.centralizer ({b} : Set (MulAut Model))) :=
      fun f => ⟨f.val.val, f.val.property, by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hh : b * f.val * b⁻¹ * (f.val : MulAut Model)⁻¹ = 1 :=
          congrArg Subtype.val f.property
        have hh := mul_inv_eq_one.mp hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm⟩
    have hk : Function.Injective k := by
      intro f g h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(H ⊓ Subgroup.centralizer ({b} : Set (MulAut Model))) => z.val) h
    exact (Nat.card_le_card_of_injective k hk).trans hcent
  obtain ⟨hcard, hindex, hstable, hfree⟩ := abstract_plane c hc3 h2 hn hbound hker
  let V := d.range.map H.subtype
  have hle : V ≤ H := by
    rintro f ⟨g, _, rfl⟩
    exact g.property
  have hvcard : Nat.card V = 4 :=
    (Nat.card_congr (d.range.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm.trans hcard
  have hvindex : V.relIndex H = d.range.index := by
    have hi := Subgroup.relIndex_map_map_of_injective d.range (⊤ : Subgroup H) H.subtype_injective
    simpa [V, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.relIndex_top_right] using hi
  refine ⟨V, hle, hvcard, by rwa [hvindex], ?_, ?_, ?_⟩
  · rintro f ⟨g, hg, rfl⟩
    exact ⟨c g, hstable g hg, rfl⟩
  · rintro f ⟨g, hg, rfl⟩ hgf
    exact congrArg Subtype.val (hfree g hg (Subtype.ext hgf))
  · rintro f ⟨g, hg, rfl⟩ hne x hx
    exact hfixed ⟨g, hg⟩ (fun he => hne (congrArg (fun z : d.range => (z : H).val) he)) x hx

/-- The cubic moved plane in the involution-fixing kernel of a C₄-square. -/
public theorem exists_c4_square_cubic_plane
    {B : Type*} [Group B] [Finite B]
    (e : B ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (b : MulAut B) (H : Subgroup (MulAut B))
    (hb3 : b ^ 3 = 1) (hbne : b ≠ 1)
    (hfix : ∀ f ∈ H, ∀ x : B, x ^ 2 = 1 → f x = x)
    (hnorm : ∀ f ∈ H, b * f * b⁻¹ ∈ H)
    (hcent : Nat.card (H ⊓ Subgroup.centralizer ({b} : Set (MulAut B)) :
      Subgroup (MulAut B)) ≤ 2)
    (hncomm : ¬ ∀ f ∈ H, Commute f b) :
    ∃ V : Subgroup (MulAut B), V ≤ H ∧ Nat.card V = 4 ∧
      (V.relIndex H = 1 ∨ V.relIndex H = 2) ∧
      (∀ f ∈ V, b * f * b⁻¹ ∈ V) ∧
      (∀ f ∈ V, b * f * b⁻¹ = f → f = 1) ∧
      (∀ f ∈ V, f ≠ 1 → ∀ x : B, f x = x → x ^ 2 = 1) := by
  let φ : MulAut B ≃* MulAut Model := MulAut.congr e
  let Hm := H.map φ.toMonoidHom
  have hfixm : ∀ f ∈ Hm, ∀ x : Model, x ^ 2 = 1 → f x = x := by
    rintro f ⟨g, hg, rfl⟩ x hx
    have hx' : e.symm x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    have hh := congrArg e (hfix g hg (e.symm x) hx')
    simpa [φ, MulAut.congr_apply] using hh
  have hnormm : ∀ f ∈ Hm, φ b * f * (φ b)⁻¹ ∈ Hm := by
    rintro f ⟨g, hg, rfl⟩
    exact ⟨b * g * b⁻¹, hnorm g hg, by simp⟩
  have hb3m : (φ b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hbnem : φ b ≠ 1 := fun hh => hbne (φ.injective (hh.trans (map_one φ).symm))
  have hcentm : Nat.card (Hm ⊓ Subgroup.centralizer ({φ b} : Set (MulAut Model)) :
      Subgroup (MulAut Model)) ≤ 2 := by
    let k : ↥(Hm ⊓ Subgroup.centralizer ({φ b} : Set (MulAut Model))) →
        ↥(H ⊓ Subgroup.centralizer ({b} : Set (MulAut B))) := fun f =>
      ⟨φ.symm f.val, Subgroup.mem_map_equiv.mp f.property.1, by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hh := congrArg φ.symm (Subgroup.mem_centralizer_singleton_iff.mp f.property.2)
        simpa using hh⟩
    have hk : Function.Injective k := by
      intro f g hh
      apply Subtype.ext
      apply φ.symm.injective
      exact congrArg Subtype.val hh
    exact (Nat.card_le_card_of_injective k hk).trans hcent
  have hncommm : ¬ ∀ f ∈ Hm, Commute f (φ b) := by
    intro hh
    apply hncomm
    intro f hf
    have h := (hh (φ f) ⟨f, hf, rfl⟩).map φ.symm
    simpa using h
  obtain ⟨Vm, hmle, hmcard, hmindex, hmnorm, hmfree, hmfix⟩ :=
    model_plane hb3m hbnem hfixm hnormm hcentm hncommm
  let V := Vm.map φ.symm.toMonoidHom
  have hφV (f : MulAut B) : f ∈ V ↔ φ f ∈ Vm := Subgroup.mem_map_equiv
  have hle : V ≤ H := by
    intro f hf
    have hh := hmle ((hφV f).mp hf)
    exact Subgroup.mem_map_iff_mem φ.injective |>.mp hh
  have hcard : Nat.card V = 4 :=
    (Nat.card_congr (Vm.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).toEquiv).symm.trans hmcard
  have hmap : Hm.map φ.symm.toMonoidHom = H := by
    ext f
    rw [Subgroup.mem_map_equiv]
    change φ f ∈ H.map φ.toMonoidHom ↔ f ∈ H
    exact Subgroup.mem_map_iff_mem φ.injective
  have hindex : V.relIndex H = Vm.relIndex Hm := by
    rw [← hmap]
    exact Subgroup.relIndex_map_map_of_injective Vm Hm φ.symm.injective
  refine ⟨V, hle, hcard, by rwa [hindex], ?_, ?_, ?_⟩
  · intro f hf
    apply (hφV _).mpr
    simpa using hmnorm (φ f) ((hφV f).mp hf)
  · intro f hf hh
    apply φ.injective
    have h := hmfree (φ f) ((hφV f).mp hf) (by simpa using congrArg φ hh)
    simpa using h
  · intro f hf hne x hx
    have hne' : φ f ≠ 1 := fun hh => hne (φ.injective (hh.trans (map_one φ).symm))
    have he : (φ f) (e x) = e x := by simpa [φ, MulAut.congr_apply] using congrArg e hx
    have hs := hmfix (φ f) ((hφV f).mp hf) hne' (e x) he
    apply e.injective
    simpa using hs
end C4SquareExtension
