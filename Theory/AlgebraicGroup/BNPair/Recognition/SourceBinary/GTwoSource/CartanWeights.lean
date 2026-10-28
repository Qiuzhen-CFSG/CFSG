module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanBraid

/-!
# Source Cartan--Weyl equations from the two simple-root weights

An element of H fixing the unit simple-root element commutes with the
specified source reflection. Indeed, their commutator belongs to H ∩ R_i;
write it in the aligned SL₂ torus and conjugate the rank-one word at one.
A matrix entry forces its torus parameter to be one, also over F₂.
Taking a square root in the finite characteristic-two field therefore
identifies the reflection commutator of any prescribed simple-root scalar.

Apply this to h(l,m) on E and F to obtain both Weyl actions on the torus.
Transport the two simple-root weights through the already proved reflection
interchanges to obtain all six weights. The required simple-root weights
in turn follow from two explicit common-field cross actions: the short
coroot acts on E by a⁻³ and the long coroot acts on F by a⁻¹. The own-root
square actions are supplied by the actual SL₂ pinnings. The full H is
abelian by the existing SplitData hypothesis; no new abelianness premise
is required in the application.

Together with CartanBraid this completes every presentation clause from
the still-explicit lower positive equations and these two cross actions.
It does not prove the coupled-module construction supplying them, nor the
6E(a) -> 9A source theorem. WeightApplication connects the result to the
literal full marked comparison, without excluding q=2 or q=4.

Source: Fong--Seitz II §7, printed p.192, and (9.9)--(9.21), printed
pp.213--217. All formulas use the consumer's left-conjugation convention.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
include hK μ n

/-- A Cartan element fixing the unit simple-root element commutes with its
specified source reflection. This includes the binary rank-one group. -/
theorem cartan_commutes_reflection_of_fixes_one (i : Fin 2) {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (hu : t * alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd 1) * t⁻¹ =
      alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd 1)) :
    Commute t ((n i).val : X ⧸ Q.D) := by
  let w : X ⧸ Q.D := (n i).val
  let f := alignedPinningHom Q split i (hK i) (μ i) (n i)
  let c := t*w*t⁻¹*w⁻¹
  have hcR : c ∈ rankOne Q split i :=
    (rankOne Q split i).mul_mem
      ((mem_normalizer_iff.mp (rankOne_torus_normalizes Q split i ht) w).mp (n i).mem_rankOne)
      ((rankOne Q split i).inv_mem (n i).mem_rankOne)
  have hnH : w ∈ normalizer (Q.tits.B ⊓ Q.tits.N : Set (X ⧸ Q.D)) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mp Q.tits.intersection_normal (n i).val.property
  have hcH : c ∈ Q.tits.B ⊓ Q.tits.N := by
    change t*w*t⁻¹*w⁻¹ ∈ _
    rw [mul_assoc t w t⁻¹, mul_assoc]
    exact (Q.tits.B ⊓ Q.tits.N).mul_mem ht
      ((mem_normalizer_iff.mp hnH t⁻¹).mp ((Q.tits.B ⊓ Q.tits.N).inv_mem ht))
  obtain ⟨b,hb⟩ := exists_alignedTorus_of_mem Q split i (hK i) (μ i) (n i) hcH hcR
  have hw : MulAut.conj t w = f (tor b * weyl F) := by
    rw [map_mul]
    change t*w*t⁻¹ = alignedTorus Q split i (hK i) (μ i) (n i) b * f (weyl F)
    rw [hb,alignedPinningHom_weyl]
    change t*w*t⁻¹ = (t*w*t⁻¹*w⁻¹)*w
    group
  have hword := aligned_rankOne_word Q split i (hK i) (μ i) (n i) (1 : Fˣ)
  have he := congrArg (MulAut.conj t) hword
  change MulAut.conj t (f (uni 1) * (w*f (uni 1)*w⁻¹) * f (uni 1)) =
    MulAut.conj t (f (tor 1)*w) at he
  have hu' : MulAut.conj t (f (uni 1)) = f (uni 1) := hu
  simp only [map_mul,map_inv,hu',hw] at he
  have ht1 : tor (1 : Fˣ) = 1 := by ext j k; fin_cases j <;> fin_cases k <;> simp
  rw [ht1,map_one,map_one,one_mul] at he
  have hm := (alignedPinningHom_injective Q split i (hK i) (μ i) (n i))
    (show f (uni 1 * ((tor b*weyl F)*uni 1*(tor b*weyl F)⁻¹)*uni 1) = f (tor b*weyl F) by
      simpa only [map_mul,map_inv] using he)
  have hentry := congrArg (fun g : SL2 F => g.val 0 0) hm
  have hb2 : (b : F)⁻¹^2 = 1 := by
    have hh : 1 + (b : F)⁻¹ * (b : F)⁻¹ = 0 := by
      simpa [Matrix.mul_apply,Fin.sum_univ_two,CharTwo.neg_eq] using hentry
    simpa only [pow_two] using (CharTwo.add_eq_zero.mp hh).symm
  have hb1 : b = 1 := by
    apply Units.ext
    have hi : (b : F)⁻¹ = 1 := CharTwo.sq_injective (hb2.trans (one_pow 2).symm)
    simpa only [inv_inv,inv_one,Units.val_one] using congrArg Inv.inv hi
  have hw' : MulAut.conj t w = w := by
    rw [hw,hb1,ht1,one_mul]
    exact alignedPinningHom_weyl Q split i (hK i) (μ i) (n i)
  exact (mul_inv_eq_iff_eq_mul.mp hw')


/-- The rank-one scalar on the unit root determines the Cartan-reflection
commutator in the same aligned pinning. -/
theorem reflection_cartan_of_simple_weight (i : Fin 2) {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N) (a : Fˣ)
    (hu : t * alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd 1) * t⁻¹ =
      alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd (a : F))) :
    (n i).val * t * ((n i).val : X ⧸ Q.D)⁻¹ =
      t * alignedTorusHom Q split i (hK i) (μ i) (n i) a⁻¹ := by
  have hinj : Function.Injective (fun b : Fˣ => b^2) := by
    intro b c he
    apply Units.ext
    apply CharTwo.sq_injective
    exact congrArg Units.val he
  obtain ⟨b,hb⟩ := (Finite.surjective_of_injective hinj) a
  change b^2 = a at hb
  let T := alignedTorusHom Q split i (hK i) (μ i) (n i)
  let w : X ⧸ Q.D := (n i).val
  have hbF : (b : F)^2 = (a : F) := congrArg Units.val hb
  have hcH : T b⁻¹ * t ∈ Q.tits.B ⊓ Q.tits.N :=
    (Q.tits.B ⊓ Q.tits.N).mul_mem (alignedTorus_mem_cartan Q split i (hK i) (μ i) (n i) b⁻¹) ht
  have hcu : (T b⁻¹ * t) * alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd 1) *
      (T b⁻¹ * t)⁻¹ = alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd 1) := by
    have he := alignedTorus_root Q split i (hK i) (μ i) (n i) b⁻¹ (a : F)
    have ha : (↑b⁻¹ : F)^2 * (a : F) = 1 := by
      rw [Units.val_inv_eq_inv_val,← hbF,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ b.ne_zero)]
    rw [ha] at he
    calc
      _ = T b⁻¹ * (t * alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd 1) * t⁻¹) *
          (T b⁻¹)⁻¹ := by group
      _ = _ := by rw [hu]; exact he
  have hc := cartan_commutes_reflection_of_fixes_one Q split hK μ n i hcH hcu
  have hw : T b * (w*t*w⁻¹) = T b⁻¹*t := by
    have he : w*(T b⁻¹*t)*w⁻¹ = T b⁻¹*t := by
      rw [← hc.eq,mul_assoc,mul_inv_cancel,mul_one]
    have hh := reflection_alignedTorus Q split i (hK i) (μ i) (n i) b⁻¹
    simp only [inv_inv] at hh
    change w*T b⁻¹*w⁻¹ = T b at hh
    calc
      _ = (w*T b⁻¹*w⁻¹)*(w*t*w⁻¹) := by rw [hh]
      _ = _ := by simpa only [mul_assoc,inv_mul_cancel_left] using he
  calc
    w*t*w⁻¹ = T b⁻¹ * (T b * (w*t*w⁻¹)) := by
      rw [← mul_assoc,← map_mul,inv_mul_cancel,map_one,one_mul]
    _ = T b⁻¹ * (T b⁻¹*t) := by rw [hw]
    _ = T a⁻¹ * t := by rw [← mul_assoc,← map_mul,← pow_two,inv_pow,hb]
    _ = t * T a⁻¹ := by
      let := split.abelian
      exact congrArg Subtype.val (mul_comm
        (⟨_,alignedTorus_mem_cartan Q split i (hK i) (μ i) (n i) a⁻¹⟩ : ↥(Q.tits.B ⊓ Q.tits.N))
        (⟨t,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N)))


variable (hH : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N))
local notation "d" => sourceBorelWeyl Q split hK μ n short hH

/-- The long simple-root scalar forces the full long Weyl action on the torus. -/
theorem sourceBorelWeyl_r_torus_of_simple_weight
    (hE : ∀ l m, (d).torus (l,m) * (d).x 4 1 * ((d).torus (l,m))⁻¹ =
      (d).x 4 ((m : F)^2/l)) (l m : Fˣ) :
    (d).r * (d).torus (l,m) * (d).r⁻¹ = (d).torus (l,l/m) := by
  have he := reflection_cartan_of_simple_weight Q split hK μ n (1-short)
    (alignedPairTorus_mem Q split hK μ n short hH (l,m)) (m^2/l)
    (by
      have hh := hE l m
      dsimp only [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,Matrix.cons_val] at hh ⊢
      simpa only [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val] using hh)
  change (d).r * (d).torus (l,m) * (d).r⁻¹ = _ at he
  rw [he]
  change (alignedTorusHom Q split short (hK short) (μ short) (n short) l *
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (l*m)) *
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (m^2/l)⁻¹ =
    alignedTorusHom Q split short (hK short) (μ short) (n short) l *
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (l*(l/m))
  rw [mul_assoc,← map_mul]
  congr 2
  apply Units.ext
  simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val]
  field_simp

/-- The short simple-root scalar forces the full short Weyl action on the torus. -/
theorem sourceBorelWeyl_s_torus_of_simple_weight
    (hF : ∀ l m, (d).torus (l,m) * (d).x 5 1 * ((d).torus (l,m))⁻¹ =
      (d).x 5 ((l : F)/m)) (l m : Fˣ) :
    (d).s * (d).torus (l,m) * (d).s⁻¹ = (d).torus (m,l) := by
  have he := reflection_cartan_of_simple_weight Q split hK μ n short
    (alignedPairTorus_mem Q split hK μ n short hH (l,m)) (l/m)
    (by
      have hh := hF l m
      dsimp only [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,Matrix.cons_val] at hh ⊢
      simpa only [Units.val_div_eq_div_val] using hh)
  change (d).s * (d).torus (l,m) * (d).s⁻¹ = _ at he
  rw [he]
  change (alignedTorusHom Q split short (hK short) (μ short) (n short) l *
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (l*m)) *
      alignedTorusHom Q split short (hK short) (μ short) (n short) (l/m)⁻¹ =
    alignedTorusHom Q split short (hK short) (μ short) (n short) m *
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (m*l)
  rw [mul_assoc,← (alignedTori_commute Q split hK μ n short hH (l/m)⁻¹ (l*m)).eq,
    ← mul_assoc,← map_mul]
  have hu : l*(l/m)⁻¹ = m := by
    apply Units.ext
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_div_eq_div_val]
    field_simp
  rw [hu,mul_comm l m]

omit hK μ n [Field F] [Finite F] [CharP F 2] in
private theorem weight_transfer {Y : Type*} [Group Y] (w t t' : Y) (f g : F → Y)
    (hw : w^2 = 1) (ht : w*t*w⁻¹ = t') (hf : ∀ a, w*f a*w⁻¹ = g a)
    (a b : F) (ha : t'*f a*t'⁻¹ = f b) : t*g a*t⁻¹ = g b := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
  have hi (x : Y) : MulAut.conj w (MulAut.conj w x) = x := by
    change w*(w*x*w⁻¹)*w⁻¹ = x
    rw [hw']
    calc
      _ = (w*w)*x*(w*w) := by group
      _ = x := by rw [← pow_two,hw,one_mul,mul_one]
  have ht' : MulAut.conj w t = t' := ht
  have hf' (a : F) : MulAut.conj w (f a) = g a := hf a
  apply (MulAut.conj w).injective
  simp only [map_mul,map_inv,ht',← hf',hi]
  exact ha

/-- The two simple-root weights determine all six weights by the source
reflection transports; no positive commutator equation is used here. -/
theorem sourceBorelWeyl_torus_root_of_simple_weights
    (hE : ∀ l m a, (d).torus (l,m) * (d).x 4 a * ((d).torus (l,m))⁻¹ =
      (d).x 4 ((m : F)^2/l*a))
    (hF : ∀ l m a, (d).torus (l,m) * (d).x 5 a * ((d).torus (l,m))⁻¹ =
      (d).x 5 ((l : F)/m*a)) (l m : Fˣ) (i : Fin 6) (a : F) :
    (d).torus (l,m) * (d).x i a * ((d).torus (l,m))⁻¹ =
      (d).x i (BorelWeylData.weight l m i * a) := by
  have hr := sourceBorelWeyl_r_torus_of_simple_weight Q split hK μ n short hH
    (fun l m => by simpa only [mul_one] using hE l m 1)
  have hs := sourceBorelWeyl_s_torus_of_simple_weight Q split hK μ n short hH
    (fun l m => by simpa only [mul_one] using hF l m 1)
  have hD (l m : Fˣ) : (d).torus (l,m)*(d).x 3 a*((d).torus (l,m))⁻¹ = (d).x 3 ((m : F)*a) := by
    have he := weight_transfer (d).r ((d).torus (l,m)) ((d).torus (l,l/m))
      ((d).x 5) ((d).x 3) (sourceBorelWeyl_r_sq Q split hK μ n short hH) (hr l m)
      (sourceBorelWeyl_rF Q split hK μ n short hH) a _ (hF l (l/m) a)
    have hscalar : (l : F) / (↑(l/m) : F) * a = (m : F)*a := by
      simp only [Units.val_div_eq_div_val]; field_simp
    rwa [hscalar] at he
  have hC : (d).torus (l,m)*(d).x 2 a*((d).torus (l,m))⁻¹ = (d).x 2 ((l : F)*a) :=
    weight_transfer (d).s ((d).torus (l,m)) ((d).torus (m,l)) ((d).x 3) ((d).x 2)
      (sourceBorelWeyl_s_sq Q split hK μ n short hH) (hs l m)
      (sourceBorelWeyl_sD Q split hK μ n short hH) a _ (hD m l)
  have hB (l m : Fˣ) : (d).torus (l,m)*(d).x 1 a*((d).torus (l,m))⁻¹ = (d).x 1 ((l : F)^2/m*a) :=
    weight_transfer (d).s ((d).torus (l,m)) ((d).torus (m,l)) ((d).x 4) ((d).x 1)
      (sourceBorelWeyl_s_sq Q split hK μ n short hH) (hs l m)
      (sourceBorelWeyl_sE Q split hK μ n short hH) a _ (hE m l a)
  have hA : (d).torus (l,m)*(d).x 0 a*((d).torus (l,m))⁻¹ = (d).x 0 ((l : F)*m*a) := by
    have he := weight_transfer (d).r ((d).torus (l,m)) ((d).torus (l,l/m))
      ((d).x 1) ((d).x 0) (sourceBorelWeyl_r_sq Q split hK μ n short hH) (hr l m)
      (sourceBorelWeyl_rB Q split hK μ n short hH) a _ (hB l (l/m))
    have hscalar : (l : F)^2 / (↑(l/m) : F) * a = (l : F)*m*a := by
      simp only [Units.val_div_eq_div_val]; field_simp
    rwa [hscalar] at he
  fin_cases i
  · exact hA
  · exact hB l m
  · exact hC
  · exact hD l m
  · exact hE l m a
  · exact hF l m a


/-- The cross actions are the exact common-field scalars still required from
the coupled modules. The own-root scalars already follow from SL₂. -/
theorem sourceBorelWeyl_simple_weights_of_cross_actions
    (hshort : ∀ (a : Fˣ) (b : F),
      alignedTorusHom Q split short (hK short) (μ short) (n short) a * (d).x 4 b *
        (alignedTorusHom Q split short (hK short) (μ short) (n short) a)⁻¹ =
          (d).x 4 ((a : F)⁻¹^3*b))
    (hlong : ∀ (a : Fˣ) (b : F),
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a * (d).x 5 b *
        (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)⁻¹ =
          (d).x 5 ((a : F)⁻¹*b)) :
    (∀ l m a, (d).torus (l,m) * (d).x 4 a * ((d).torus (l,m))⁻¹ =
      (d).x 4 ((m : F)^2/l*a)) ∧
    (∀ l m a, (d).torus (l,m) * (d).x 5 a * ((d).torus (l,m))⁻¹ =
      (d).x 5 ((l : F)/m*a)) := by
  let Ts := alignedTorusHom Q split short (hK short) (μ short) (n short)
  let Tr := alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
  have ownE (a : Fˣ) (b : F) : Tr a * (d).x 4 b * (Tr a)⁻¹ = (d).x 4 ((a : F)^2*b) :=
    alignedTorus_root Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a b
  have ownF (a : Fˣ) (b : F) : Ts a * (d).x 5 b * (Ts a)⁻¹ = (d).x 5 ((a : F)^2*b) :=
    alignedTorus_root Q split short (hK short) (μ short) (n short) a b
  have ht (l m : Fˣ) : (d).torus (l,m) = Ts l * Tr (l*m) := rfl
  constructor
  · intro l m a
    rw [ht]
    calc
      _ = Ts l * (Tr (l*m) * (d).x 4 a * (Tr (l*m))⁻¹) * (Ts l)⁻¹ := by group
      _ = (d).x 4 ((l : F)⁻¹^3*((↑(l*m) : F)^2*a)) := by rw [ownE,hshort]
      _ = _ := by congr 1; simp only [Units.val_mul]; field_simp
  · intro l m a
    rw [ht]
    calc
      _ = Ts l * (Tr (l*m) * (d).x 5 a * (Tr (l*m))⁻¹) * (Ts l)⁻¹ := by group
      _ = (d).x 5 ((l : F)^2*((↑(l*m) : F)⁻¹*a)) := by rw [hlong,ownF]
      _ = _ := by congr 1; simp only [Units.val_mul]; field_simp

/-- All Borel--Weyl clauses follow from the lower positive construction and
the two simple-root torus actions. Those source module premises remain explicit. -/
theorem sourceBorelWeyl_relations_of_simple_weights (hm : rotationOrder Q = 6)
    (d₀ : PartialPositiveData (alignedSourceRoots Q split hK μ n short))
    (hE : ∀ l m a, (d).torus (l,m) * (d).x 4 a * ((d).torus (l,m))⁻¹ =
      (d).x 4 ((m : F)^2/l*a))
    (hF : ∀ l m a, (d).torus (l,m) * (d).x 5 a * ((d).torus (l,m))⁻¹ =
      (d).x 5 ((l : F)/m*a)) : (d).Relations where
  toCharTwoRelations := aligned_positive_relations_of_partial Q split hK μ n short hm d₀
  torus_root := sourceBorelWeyl_torus_root_of_simple_weights Q split hK μ n short hH hE hF
  r_sq := sourceBorelWeyl_r_sq Q split hK μ n short hH
  s_sq := sourceBorelWeyl_s_sq Q split hK μ n short hH
  braid := sourceBorelWeyl_braid Q split hK μ n short hH hm d₀.commuting
  r_torus := sourceBorelWeyl_r_torus_of_simple_weight Q split hK μ n short hH
    (fun l m => by simpa only [mul_one] using hE l m 1)
  s_torus := sourceBorelWeyl_s_torus_of_simple_weight Q split hK μ n short hH
    (fun l m => by simpa only [mul_one] using hF l m 1)
  rA := sourceBorelWeyl_rA Q split hK μ n short hH
  rB := sourceBorelWeyl_rB Q split hK μ n short hH
  rC := sourceBorelWeyl_rC Q split hK μ n short hH hm d₀.commuting
  rD := sourceBorelWeyl_rD Q split hK μ n short hH
  rF := sourceBorelWeyl_rF Q split hK μ n short hH
  sA := sourceBorelWeyl_sA Q split hK μ n short hH hm d₀.commuting
  sB := sourceBorelWeyl_sB Q split hK μ n short hH
  sC := sourceBorelWeyl_sC Q split hK μ n short hH
  sD := sourceBorelWeyl_sD Q split hK μ n short hH
  sE := sourceBorelWeyl_sE Q split hK μ n short hH
  long_word := sourceBorelWeyl_long_word Q split hK μ n short hH
  short_word := sourceBorelWeyl_short_word Q split hK μ n short hH

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
