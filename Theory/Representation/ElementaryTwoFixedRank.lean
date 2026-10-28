module
public import Theory.Representation.InvolutiveWeights
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.BinaryCodeFixedTwo

/-!
# Elementary two-actions with fixed spaces of dimension at most two

Let an elementary abelian two-group act faithfully on a finite-dimensional
vector space over a field where two is nonzero. If every nonidentity actor
fixes a space of dimension at most two, the actor group has order at most
eight. At order eight one of its nonidentity elements acts as minus identity.

The occurring character spaces span over the original field by the genuine
exponent-two decomposition. Their characters take only the values ±1 and
separate actors. Distinct character spaces are independent, so the number of
characters fixed by an actor is bounded by its fixed-space dimension.
Encoding the signs as binary coordinates reduces to the three-coordinate
projection argument: no nonidentity word fixes three coordinates. At order
eight that projection is onto, and the product of its three coordinate lifts
has every sign negative. Spanning converts this word to minus identity on the
whole original space.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma A.1.28, printed p.26. The source applies this theorem to the actual
odd-prime Frattini quotient of its supercritical subgroup. No assertion about
direct sums for arbitrary abelian actors is used.
-/

open scoped IsMulCommutative
namespace Representation.ElementaryTwoFixedRank
variable {K A V : Type*} [Field K] [Group A] [AddCommGroup V] [Module K V]

private theorem character_eq_neg_one (χ : A →* Kˣ) (hpow : ∀ a : A, a^2=1)
    {a : A} (ha : χ a ≠ 1) : (χ a : K) = -1 := by
  have hs : (χ a : K)^2=1 := by
    have h := congrArg (fun x : Kˣ => (x : K)) (show χ a ^ 2 = 1 by rw [←map_pow,hpow,map_one])
    exact h
  exact (sq_eq_one_iff.mp hs).resolve_left (fun h => ha (Units.ext h))

private noncomputable def signCharacter (χ : A →* Kˣ) (hpow : ∀ a : A, a^2=1) :
    A →* Multiplicative (ZMod 2) := by
  classical
  exact
    { toFun := fun a => if χ a = 1 then 1 else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := by
        intro a b
        by_cases ha : χ a = 1 <;> by_cases hb : χ b = 1
        · simp [map_mul,ha,hb]
        · simp [map_mul,ha,hb]
        · simp [map_mul,ha,hb]
        · have hab : χ (a*b) = 1 := by
            apply Units.ext
            rw [map_mul,Units.val_mul,character_eq_neg_one χ hpow ha,character_eq_neg_one χ hpow hb]
            simp
          simp only [hab,ha,hb,if_pos]
          decide }

private theorem signCharacter_eq_one_iff (χ : A →* Kˣ) (hpow : ∀ a : A, a^2=1) (a : A) :
    signCharacter χ hpow a = 1 ↔ χ a = 1 := by
  classical
  change (if χ a = 1 then (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) = 1 ↔ _
  split_ifs <;> simp_all

private theorem signCharacter_eq_imp (χ : A →* Kˣ) (hpow : ∀ a : A, a^2=1) (a b : A)
    (he : signCharacter χ hpow a = signCharacter χ hpow b) : χ a = χ b := by
  by_cases hx : χ a = 1
  · have hy := (signCharacter_eq_one_iff χ hpow b).mp (he.symm.trans ((signCharacter_eq_one_iff χ hpow a).mpr hx))
    exact hx.trans hy.symm
  · have hy : χ b ≠ 1 := fun h => hx ((signCharacter_eq_one_iff χ hpow a).mp (he.trans ((signCharacter_eq_one_iff χ hpow b).mpr h)))
    exact Units.ext ((character_eq_neg_one χ hpow hx).trans (character_eq_neg_one χ hpow hy).symm)

variable [Finite A] [IsElementaryAbelian 2 A] [FiniteDimensional K V]

private theorem card_cast_ne_zero (h2 : (2 : K) ≠ 0) : (Nat.card A : K) ≠ 0 := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [hn,Nat.cast_pow]
  exact pow_ne_zero n h2

private theorem fixed_weight_count (ρ : Representation K A V)
    (h2 : (2 : K) ≠ 0) (a : A) :
    Nat.card {χ : ρ.CharacterWeight // χ.val a = 1} ≤
      Module.finrank K (Module.End.eigenspace (ρ a) 1) := by
  classical
  let I := {χ : ρ.CharacterWeight // χ.val a = 1}
  have horder : (Nat.card A : K) ≠ 0 := card_cast_ne_zero h2
  let := (ρ.characterWeight_card_le horder).1
  let : Fintype I := Fintype.ofFinite I
  have hnon (i : I) : ∃ v : V, v ∈ ρ.characterWeightSpace i.val.val ∧ v ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot i.val.property
  choose v hv hvne using hnon
  have hind : iSupIndep (fun i : I => ρ.characterWeightSpace i.val.val) :=
    (ρ.characterWeightSpace_independent horder).comp (Subtype.val_injective.comp Subtype.val_injective)
  have hlin : LinearIndependent K v := hind.linearIndependent _ hv hvne
  have hvfix (i : I) : v i ∈ Module.End.eigenspace (ρ a) 1 := by
    have hi := hv i
    simp only [Representation.characterWeightSpace,Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] at hi
    rw [Module.End.mem_eigenspace_iff]
    simpa only [i.property,Units.val_one] using hi a
  let w : I → Module.End.eigenspace (ρ a) 1 := fun i => ⟨v i,hvfix i⟩
  have hw : LinearIndependent K w := LinearIndependent.of_comp (Module.End.eigenspace (ρ a) 1).subtype hlin
  simpa only [Nat.card_eq_fintype_card] using hw.fintype_card_le_finrank

private theorem sign_encoding (ρ : Representation K A V)
    (hρ : Function.Injective ρ) (h2 : (2 : K) ≠ 0)
    (hfix : ∀ a : A, a ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ a) 1) ≤ 2) :
    ∃ f : A →* (ρ.CharacterWeight → Multiplicative (ZMod 2)),
      Function.Injective f ∧
      (∀ a : A, a ≠ 1 → Nat.card {χ : ρ.CharacterWeight // f a χ = 1} ≤ 2) ∧
      (∀ a : A, (∀ χ : ρ.CharacterWeight, f a χ = Multiplicative.ofAdd 1) →
        ∀ v : V, ρ a v = -v) := by
  classical
  have hpow (a : A) : a^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a
  let f : A →* (ρ.CharacterWeight → Multiplicative (ZMod 2)) :=
    { toFun := fun a χ => signCharacter χ.val hpow a
      map_one' := funext (fun χ => map_one (signCharacter χ.val hpow))
      map_mul' := fun a b => funext (fun χ => map_mul (signCharacter χ.val hpow) a b) }
  refine ⟨f,?_,?_,?_⟩
  · intro a b hab
    apply ρ.eq_of_characterWeight_values_of_involutive hρ hpow h2 a b
    intro χ
    exact signCharacter_eq_imp χ.val hpow a b (congrFun hab χ)
  · intro a ha
    have he : {χ : ρ.CharacterWeight // f a χ = 1} ≃
        {χ : ρ.CharacterWeight // χ.val a = 1} :=
      { toFun := fun χ => ⟨χ.val,(signCharacter_eq_one_iff χ.val.val hpow a).mp χ.property⟩
        invFun := fun χ => ⟨χ.val,(signCharacter_eq_one_iff χ.val.val hpow a).mpr χ.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr he]
    exact (fixed_weight_count ρ h2 a).trans (hfix a ha)
  · intro a ha
    have heq : ρ a = -(1 : Module.End K V) := by
      apply LinearMap.eqLocus_eq_top.mp
      apply top_unique
      rw [← ρ.iSup_characterWeightSpace_eq_top_of_involutive hpow h2]
      refine iSup_le (fun χ v hv => ?_)
      have hχ : χ.val a ≠ 1 := by
        intro hc
        have he := (signCharacter_eq_one_iff χ.val hpow a).mpr hc
        have hcontra : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 :=
          (ha χ).symm.trans he
        exact (by decide : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1) hcontra
      have hval := character_eq_neg_one χ.val hpow hχ
      simp only [Representation.characterWeightSpace,Submodule.mem_iInf,
        Module.End.mem_eigenspace_iff] at hv
      change ρ a v = -v
      rw [hv a,hval,neg_one_smul]
    intro v
    rw [heq]
    rfl

/-- The exact order bound and inversion conclusion for the original representation. -/
public theorem card_le_eight_and_inverter
    (ρ : Representation K A V) (hρ : Function.Injective ρ) (h2 : (2 : K) ≠ 0)
    (hfix : ∀ a : A, a ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ a) 1) ≤ 2) :
    Nat.card A ≤ 8 ∧ (Nat.card A = 8 → ∃ a : A, a ≠ 1 ∧ ∀ v : V, ρ a v = -v) := by
  classical
  let := (ρ.characterWeight_card_le (card_cast_ne_zero (A := A) h2)).1
  obtain ⟨f,hf,hcount,hinv⟩ := sign_encoding ρ hρ h2 hfix
  refine ⟨BinaryCodeFixedTwo.card_le_eight f hf hcount,?_⟩
  intro hcard
  obtain ⟨a,ha⟩ := BinaryCodeFixedTwo.exists_all_nontrivial_of_card_eight f hf hcount hcard
  have hpow (b : A) : b^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) b
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨χ,_⟩ := ρ.exists_nontrivial_characterWeight_of_involutive hρ hpow h2
  refine ⟨a,?_,hinv a ha⟩
  intro ha1
  have h := ha χ
  rw [ha1,map_one] at h
  have hbad : (0 : ZMod 2) = 1 := congrArg Multiplicative.toAdd h
  exact zero_ne_one hbad

end Representation.ElementaryTwoFixedRank
