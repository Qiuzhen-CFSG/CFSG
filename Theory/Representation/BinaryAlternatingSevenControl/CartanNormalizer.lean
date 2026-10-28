module
public import Theory.Representation.BinaryAlternatingSevenControl.Offenders
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Hall-plane control of a four-dimensional A₇ offender

A subgroup of order 72 has an odd orbit on seven letters. A singleton
would put an index-five subgroup in A₆, contradicting simplicity. Thus it
preserves a triple. After marking its Sylow subgroup, this is the triple
complementary to the canonical normal four-group. A commuting three-cycle
makes that four-group a best offender on every faithful binary four-space;
uniqueness in the Sylow identifies it with the supplied offender.

An order-nine group permuting with the Sylow has join of order 72, so it
normalizes that same offender. The finite checks involve only four-group
words, subsets of seven points and distinct quadruples of four letters.

Source: Aschbacher–Smith, B.4.2(7) and 5.1.13, printed pp.90–91,637.
-/

public noncomputable section
open Subgroup Equiv
open scoped Pointwise
namespace Representation.BinaryAlternatingSevenControl.Cartan
open AlternatingSeven.DihedralLocals
local notation "A7" => alternatingGroup (Fin 7)
local notation "Perm7" => Equiv.Perm (Fin 7)
open scoped BigOperators

private theorem no_fixed (S : Subgroup A7) (hS : Nat.card S = 72) (i : Fin 7) :
    ¬ S ≤ MulAction.stabilizer A7 i := by
  intro h
  let K := MulAction.stabilizer A7 i
  let R := S.subgroupOf K
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := (AlternatingSix.SmallIndex.pointEquiv i).isSimpleGroup
  have hK : Nat.card K = 360 := by
    rw [Nat.card_congr (AlternatingSix.SmallIndex.pointEquiv i).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hR : Nat.card R = 72 := (Nat.card_congr (subgroupOfEquivOfLe h).toEquiv).trans hS
  have hi : R.index = 5 := by
    have hh := R.card_mul_index
    rw [hR,hK] at hh
    omega
  have he := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt R (by
    rw [hi,hK]; norm_num [Nat.factorial])
  rw [he,card_top,hK] at hR
  omega

private theorem fixed_triple (I : Finset (Fin 7)) (hc : I.card = 3)
    (hr : ∀ x, r x ∈ I ↔ x ∈ I)
    (hs : ∀ x, AlternatingSeven.DihedralLocals.s x ∈ I ↔ x ∈ I) :
    I = {4,5,6} := by
  revert I
  decide +kernel

private theorem small_orbit' (S : Subgroup A7) (hS : Nat.card S = 72) :
    ∃ I : Set (Fin 7), Nat.card I = 3 ∧ ∀ g ∈ S, ∀ x, g.val x ∈ I ↔ x ∈ I := by
  classical
  let Q := MulAction.orbitRel.Quotient S (Fin 7)
  let : Fintype Q := Fintype.ofFinite Q
  have hsum : (∑ q : Q, Nat.card q.orbit) = 7 := by
    simpa only [Nat.card_sigma,Nat.card_fin] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' S (Fin 7))).symm
  have hex : ∃ q : Q, ¬ 2 ∣ Nat.card q.orbit := by
    by_contra hn
    push Not at hn
    have hd := Finset.dvd_sum (fun q (_ : q ∈ Finset.univ) => hn q)
    rw [hsum] at hd
    norm_num at hd
  obtain ⟨q,hq⟩ := hex
  have hb : Nat.card q.orbit ≤ 7 := by
    simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective (fun x : q.orbit => x.val) Subtype.val_injective
  have hd : Nat.card q.orbit ∣ 72 := by
    rw [←hS,MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer S q.out)]
    exact card_quotient_dvd_card _
  have h13 : Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 3 := by
    have hn5 : Nat.card q.orbit ≠ 5 := fun h => (by decide : ¬ 5 ∣ 72) (h ▸ hd)
    have hn7 : Nat.card q.orbit ≠ 7 := fun h => (by decide : ¬ 7 ∣ 72) (h ▸ hd)
    omega
  have hinv : ∀ g ∈ S, ∀ x, g.val x ∈ q.orbit ↔ x ∈ q.orbit := by
    intro g hg x
    constructor
    · intro hx
      have hh := q.mapsTo_smul_orbit (⟨g⁻¹,S.inv_mem hg⟩ : S) hx
      change g.val⁻¹ (g.val x) ∈ q.orbit at hh
      simpa using hh
    · intro hx
      have hh := q.mapsTo_smul_orbit (⟨g,hg⟩ : S) hx
      exact hh
  rcases h13 with hc | hc
  · have hn : q.orbit.ncard = 1 := (Nat.card_coe_set_eq q.orbit).symm ▸ hc
    obtain ⟨i,hi⟩ := Set.ncard_eq_one.mp hn
    exact (no_fixed S hS i (by
      intro g hg
      have hh := (hinv g hg i).mpr (hi.symm ▸ Set.mem_singleton i)
      rw [hi] at hh
      exact hh)).elim
  · exact ⟨q.orbit,hc,hinv⟩

private theorem seventyTwo_preserves_triple (S : Subgroup A7)
    (hS : Nat.card S = 72) (hP : fixedTwoGroup ≤ S) :
    ∀ g ∈ S, ∀ x : Fin 7, g.val x ∈ ({4,5,6} : Finset (Fin 7)) ↔
      x ∈ ({4,5,6} : Finset (Fin 7)) := by
  classical
  obtain ⟨I,hi,hSI⟩ := small_orbit' S hS
  have hr : ∀ x, r x ∈ I.toFinset ↔ x ∈ I.toFinset := by
    intro x
    simpa using hSI ⟨r,twoGroup_le_alternating r_mem_twoGroup⟩ (hP r_mem_twoGroup) x
  have hs : ∀ x, AlternatingSeven.DihedralLocals.s x ∈ I.toFinset ↔ x ∈ I.toFinset := by
    intro x
    simpa using hSI ⟨_,twoGroup_le_alternating s_mem_twoGroup⟩ (hP s_mem_twoGroup) x
  have he := fixed_triple I.toFinset (by simpa using hi) hr hs
  intro g hg x
  have hh := hSI g hg x
  simpa only [←he,Set.mem_toFinset] using hh

private def eWord (i : Fin 4) : Perm7 := s ^ (i.val % 2) * (r^2) ^ (i.val / 2)
private theorem e_mul (i j : Fin 4) : ∃ k : Fin 4, eWord i * eWord j = eWord k := by
  decide +revert +kernel
private theorem e_inv (i : Fin 4) : ∃ j : Fin 4, (eWord i)⁻¹ = eWord j := by
  decide +revert +kernel
private theorem e_mem (i : Fin 4) : eWord i ∈ twoGroup :=
  twoGroup.mul_mem (twoGroup.pow_mem s_mem_twoGroup _) (twoGroup.pow_mem (twoGroup.pow_mem r_mem_twoGroup _) _)
private def E : Subgroup A7 where
  carrier := {g | ∃ i : Fin 4, eWord i = g.val}
  one_mem' := ⟨0,by decide⟩
  mul_mem' := by
    rintro a b ⟨i,hi⟩ ⟨j,hj⟩
    obtain ⟨k,hk⟩ := e_mul i j
    refine ⟨k,?_⟩
    change eWord k = a.val * b.val
    rw [←hi,←hj]
    exact hk.symm
  inv_mem' := by
    rintro a ⟨i,hi⟩
    obtain ⟨j,hj⟩ := e_inv i
    refine ⟨j,?_⟩
    change eWord j = a.val⁻¹
    rw [←hi]
    exact hj.symm
private theorem E_le : E ≤ fixedTwoGroup := by
  rintro a ⟨i,hi⟩
  change a.val ∈ twoGroup
  rw [←hi]
  exact e_mem i
private theorem E_card : Nat.card E = 4 := by
  let f : Fin 4 → E := fun i => ⟨⟨eWord i,twoGroup_le_alternating (e_mem i)⟩,i,rfl⟩
  have hi : Function.Injective eWord := by decide +kernel
  have hf : Function.Bijective f := ⟨fun i j h => hi (congrArg (fun a : E => a.val.val) h),by
    intro g
    obtain ⟨i,hi⟩ := g.property
    exact ⟨i,Subtype.ext (Subtype.ext hi)⟩⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_fin]
private theorem E_elementary : IsElementaryAbelian 2 E := by
  refine {
    toIsMulCommutative := IsMulCommutative.of_comm ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro a b
    obtain ⟨i,hi⟩ := a.property
    obtain ⟨j,hj⟩ := b.property
    apply Subtype.ext
    apply Subtype.ext
    change a.val.val * b.val.val = b.val.val * a.val.val
    rw [←hi,←hj]
    exact (by decide +kernel : ∀ i j : Fin 4, eWord i * eWord j = eWord j * eWord i) i j
  · intro a
    obtain ⟨i,hi⟩ := a.property
    apply Subtype.ext
    apply Subtype.ext
    change a.val.val ^ 2 = 1
    rw [←hi]
    exact (by decide +kernel : ∀ i : Fin 4, eWord i ^ 2 = 1) i
private def c : A7 := ⟨swap 4 5 * swap 4 6,by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private theorem c_three : c.val.IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
private theorem c_central : c ∈ centralizer (E : Set A7) := by
  intro a ha
  obtain ⟨i,hi⟩ := ha
  apply Subtype.ext
  change a.val * c.val = c.val * a.val
  rw [←hi]
  exact (by decide +kernel : ∀ i : Fin 4, eWord i * c.val = c.val * eWord i) i

private theorem e_conjugate (g : Perm7)
    (hg : ∀ x : Fin 7, g x ∈ ({4,5,6} : Finset (Fin 7)) ↔ x ∈ ({4,5,6} : Finset (Fin 7)))
    (i : Fin 4) : ∃ j : Fin 4, eWord j = g * eWord i * g⁻¹ := by
  have hb (x : Fin 4) : (g (Fin.castLE (by decide : 4 ≤ 7) x)).val < 4 := by
    have hh := (hg (Fin.castLE (by decide : 4 ≤ 7) x)).not
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    have hx := x.isLt
    have hh' : ¬ g (Fin.castLE (by decide : 4 ≤ 7) x) = 4 ∧
        ¬ g (Fin.castLE (by decide : 4 ≤ 7) x) = 5 ∧
        ¬ g (Fin.castLE (by decide : 4 ≤ 7) x) = 6 := by
      simpa only [not_or] using hh.mpr (by simp [Fin.ext_iff]; omega)
    have hy := (g (Fin.castLE (by decide : 4 ≤ 7) x)).isLt
    simp only [Fin.ext_iff] at hh'
    omega
  let v (x : Fin 4) : Fin 4 := ⟨(g (Fin.castLE (by decide : 4 ≤ 7) x)).val,hb x⟩
  have hv : Function.Injective v := by
    intro x y he
    have hh : g (Fin.castLE (by decide : 4 ≤ 7) x) = g (Fin.castLE (by decide : 4 ≤ 7) y) := Fin.ext (congrArg (fun z : Fin 4 => z.val) he)
    have hh' := g.injective hh
    exact Fin.ext (congrArg (fun z : Fin 7 => z.val) hh')
  have hh : ∀ (a b c d : Fin 4), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ j : Fin 4, eWord j = swap (Fin.castLE (by decide : 4 ≤ 7) a) (Fin.castLE (by decide : 4 ≤ 7) b) *
        swap (Fin.castLE (by decide : 4 ≤ 7) c) (Fin.castLE (by decide : 4 ≤ 7) d) := by
    decide +kernel
  have pair (a b c d : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
      ∃ j : Fin 4, eWord j = g *
        (swap (Fin.castLE (by decide : 4 ≤ 7) a) (Fin.castLE (by decide : 4 ≤ 7) b) *
         swap (Fin.castLE (by decide : 4 ≤ 7) c) (Fin.castLE (by decide : 4 ≤ 7) d)) * g⁻¹ := by
    obtain ⟨j,hj⟩ := hh (v a) (v b) (v c) (v d)
      (hv.ne hab) (hv.ne hac) (hv.ne had) (hv.ne hbc) (hv.ne hbd) (hv.ne hcd)
    refine ⟨j,?_⟩
    have he : ∀ x : Fin 4, Fin.castLE (by decide : 4 ≤ 7) (v x) = g (Fin.castLE (by decide : 4 ≤ 7) x) := fun _ => rfl
    simp only [he] at hj
    have conj_swap (x y : Fin 7) : g * swap x y * g⁻¹ = swap (g x) (g y) := by
      rw [Equiv.mul_swap_eq_swap_mul,mul_inv_cancel_right]
    calc eWord j = _ := hj
         _ = (g * swap (Fin.castLE (by decide : 4 ≤ 7) a) (Fin.castLE (by decide : 4 ≤ 7) b) * g⁻¹) *
             (g * swap (Fin.castLE (by decide : 4 ≤ 7) c) (Fin.castLE (by decide : 4 ≤ 7) d) * g⁻¹) := by
               rw [conj_swap,conj_swap]
         _ = _ := by group
  fin_cases i
  · exact ⟨0,by simp [eWord]⟩
  · exact pair 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · change ∃ j, eWord j = g * eWord (2 : Fin 4) * g⁻¹
    rw [show eWord (2 : Fin 4) = swap 0 2 * swap 1 3 by decide +kernel]
    exact pair 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · change ∃ j, eWord j = g * eWord (3 : Fin 4) * g⁻¹
    rw [show eWord (3 : Fin 4) = swap 0 3 * swap 1 2 by decide +kernel]
    exact pair 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem preserves_normalizes (g : A7)
    (hg : ∀ x : Fin 7, g.val x ∈ ({4,5,6} : Finset (Fin 7)) ↔ x ∈ ({4,5,6} : Finset (Fin 7))) :
    g ∈ normalizer (E : Set A7) := by
  apply mem_normalizer_iff.mpr
  intro a
  change (∃ i, eWord i = a.val) ↔ ∃ i, eWord i = g.val * a.val * g.val⁻¹
  constructor
  · rintro ⟨i,hi⟩
    rw [←hi]
    exact e_conjugate g.val hg i
  · rintro ⟨i,hi⟩
    obtain ⟨j,hj⟩ := e_conjugate g.val⁻¹ (fun x => by simpa using (hg (g.val⁻¹ x)).symm) i
    refine ⟨j,?_⟩
    rw [hi] at hj
    simpa only [inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using hj

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
open Representation.BinaryOffender
private theorem fixed_rank_two_of_central_cubic
    (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {A : Subgroup A7} (hA : IsElementaryTwo A)
    (c : A7) (hc : c ∈ centralizer (A : Set A7))
    (hthree : (c : Equiv.Perm (Fin 7)).IsThreeCycle) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) = 2 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) V)
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨v,hv,hfix⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
    (ρ.comp A.subtype) (IsElementaryAbelian.isPGroup 2 A)
  have hcv : ρ c v ∈ fixedSpace ρ A := by
    intro a
    change ρ (a : A7) (ρ c v) = ρ c v
    rw [← Module.End.mul_apply, ← map_mul,hc a a.property,map_mul,Module.End.mul_apply]
    exact congrArg (ρ c) (hfix a)
  have hn : ρ c v ≠ 0 := by
    intro hz
    apply hv
    simpa only [ρ.inv_self_apply,map_zero] using congrArg (ρ c⁻¹) hz
  have hne : ρ c v ≠ v := fun he =>
    hv (binaryAlternatingSeven_threeCycle_fixedPointFree ρ hf hd c hthree v he)
  let W := fixedSpace ρ A
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Fintype W := Fintype.ofFinite W
  have hcard : 2 < Nat.card W := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.two_lt_card_iff.mpr
    refine ⟨0,⟨v,hfix⟩,⟨ρ c v,hcv⟩,?_,?_,?_⟩
    · exact fun he => hv (congrArg Subtype.val he).symm
    · exact fun he => hn (congrArg Subtype.val he).symm
    · exact fun he => hne (congrArg Subtype.val he).symm
  have hl : 2 ≤ Module.finrank (ZMod 2) W := by
    by_contra h
    have hd1 : Module.finrank (ZMod 2) W ≤ 1 := by omega
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    norm_num at hh
    omega
  have hc := fixedCodim_add_finrank ρ A
  have hh := elementary_two_le_codim ρ hf hd hA
  change Module.finrank (ZMod 2) W = 2
  change fixedCodim ρ A + Module.finrank (ZMod 2) W = _ at hc
  omega


private theorem E_best (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) : IsBestOffender ρ E := by
  have hE : IsElementaryTwo E := ⟨by intro he; have hh := E_card; rw [he,card_bot] at hh; omega,E_elementary⟩
  have hr : rank E = 2 := by
    have hh := hE.card_eq_two_pow_rank
    rw [E_card] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hh.symm
  have hfix := fixed_rank_two_of_central_cubic ρ hf hd hE c c_central c_three
  apply (isBestOffender_iff_of_not_strong ρ (no_strong_offender ρ hf hd) E).mpr
  refine ⟨hE,?_⟩
  have hh := fixedCodim_add_finrank ρ E
  omega

/-- Every order-72 subgroup containing the chosen Sylow normalizes its best offender. -/
theorem seventyTwo_normalizes_best (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (P : Sylow 2 A7) (A S : Subgroup A7) (hAP : A ≤ P) (hA : IsBestOffender ρ A)
    (hPS : (P : Subgroup A7) ≤ S) (hS : Nat.card S = 72) : S ≤ normalizer (A : Set A7) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A7 P fixedSylow
  let f := (MulAut.conj g).toMonoidHom
  have hP : (P : Subgroup A7).map f = fixedTwoGroup := congrArg Sylow.toSubgroup hg
  have hAP' : A.map f ≤ fixedTwoGroup := hP ▸ map_mono hAP
  have hAE : A.map f = E := best_unique_in_sylow ρ hf hd fixedSylow hAP' E_le
    (hA.map_conj ρ g) (E_best ρ hf hd)
  have hS' : Nat.card (S.map f) = 72 := (card_map_of_injective (MulAut.conj g).injective).trans hS
  have hn : S.map f ≤ normalizer (E : Set A7) := fun x hx =>
    preserves_normalizes x (seventyTwo_preserves_triple (S.map f) hS' (hP ▸ map_mono hPS) x hx)
  rw [←hAE,←map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hn

/-- A three-plane permuting with the full Sylow normalizes the same offender. -/
theorem permuting_plane_normalizes_best (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (P : Sylow 2 A7) (A R : Subgroup A7) (hAP : A ≤ P) (hA : IsBestOffender ρ A)
    (hR : Nat.card R = 9)
    (hperm : (R : Set A7) * (P : Set A7) = (P : Set A7) * (R : Set A7)) :
    R ⊔ (P : Subgroup A7) ≤ normalizer (A : Set A7) := by
  have hcP : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_eq_fintype_card]
    norm_num [Nat.factorial]
    rw [show (2520 : ℕ).factorization 2 = 3 by
      rw [show 2520 = 2^3*315 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]]
    norm_num
  have hdis := (IsPGroup.of_card (p := 3) (n := 2) hR).disjoint_of_coprime P.isPGroup' (by decide)
  have hc := card_set_mul_mul_card_inf R (P : Subgroup A7)
  rw [hdis.eq_bot,card_bot,mul_one,←coe_sup_of_set_mul_comm R (P : Subgroup A7) hperm,hR,hcP] at hc
  exact seventyTwo_normalizes_best ρ hf hd P A (R ⊔ (P : Subgroup A7)) hAP hA le_sup_right hc

private theorem odd_three_order (g : Equiv.Perm (Fin 7))
    (ho : Odd (orderOf g)) (h3 : 3 ∣ orderOf g) : orderOf g = 3 := by
  have hc (c : ℕ) (hc : c ∈ g.cycleType) : c = 3 ∨ c = 5 ∨ c = 7 := by
    have hb : c ≤ 7 := (Multiset.le_sum_of_mem hc).trans (by simpa using g.sum_cycleType_le)
    have hl := Equiv.Perm.two_le_of_mem_cycleType hc
    obtain ⟨k,hk⟩ := ho.of_dvd_nat (Equiv.Perm.dvd_of_mem_cycleType hc)
    omega
  have hm : 3 ∈ g.cycleType := by
    by_contra hn
    have hd : orderOf g ∣ 35 := by
      rw [←g.lcm_cycleType]
      apply Multiset.lcm_dvd.mpr
      intro c hcm
      rcases hc c hcm with rfl | rfl | rfl
      · exact (hn hcm).elim
      · decide
      · decide
    exact (by decide : ¬ 3 ∣ 35) (h3.trans hd)
  have hp : g ^ 3 = 1 := by
    apply Equiv.Perm.pow_prime_eq_one_iff.mpr
    intro c hcm
    obtain ⟨S,hS⟩ := Multiset.exists_cons_of_mem hm
    have hs : 3 + S.sum ≤ 7 := by simpa [hS] using g.sum_cycleType_le
    rw [hS,Multiset.mem_cons] at hcm
    rcases hcm with rfl | hcm
    · rfl
    · have hb := Multiset.le_sum_of_mem hcm
      have hl := hc c (by rw [hS]; exact Multiset.mem_cons.mpr (Or.inr hcm))
      omega
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hp) h3

/-- An odd cyclic subgroup on seven letters containing a cubic has order three. -/
theorem odd_cyclic_card_three (R : Subgroup (alternatingGroup (Fin 7))) [IsCyclic R]
    (ho : Odd (Nat.card R)) (h3 : 3 ∣ Nat.card R) : Nat.card R = 3 := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := R)
  have he : orderOf g.val.val = Nat.card R :=
    (Subgroup.orderOf_coe g.val).trans ((Subgroup.orderOf_coe g).trans hg)
  exact he.symm.trans (odd_three_order g.val.val (he.symm ▸ ho) (he.symm ▸ h3))

end Representation.BinaryAlternatingSevenControl.Cartan
