module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportPermutation
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.RestrictedInvertedSupport

/-!
# The displacement budget in the small-three branch

For D.2.25, a transposition of canonical planes consumes the involution's
whole two-dimensional displacement and therefore fixes the canonical fixed
complement. If every factor is normalized, inversion of a chosen plane
consumes one dimension. A moved fixed complement consumes the other, so all
remaining canonical planes are fixed. An inverted cubic lies in the same
permutation kernel and acts trivially on those remaining planes.

The restriction identities retain the literal ambient commutator. They
allow the residual cubic witness to be used without assuming faithfulness
on the fixed complement.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.25, printed p.190, `refs/quasithin.pdf`.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]

private theorem displacement_le_support (T : Subgroup G) (U : Subgroup V)
    (hU : IsInvariant T V U) : commutatorSubgroup T V U ≤ U := by
  rw [commutatorSubgroup, Subgroup.closure_le]
  rintro _ ⟨a, v, hv, rfl⟩
  exact U.mul_mem (U.inv_mem hv) ((hU.invariant a v).mp hv)

private theorem displacement_le_full (T : Subgroup G) (U : Subgroup V) :
    commutatorSubgroup T V U ≤ commutatorAction T V := by
  rw [commutatorSubgroup, commutatorAction_eq_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨a,v,_,rfl⟩
  exact ⟨a,v,rfl⟩

private theorem fixed_mono {P Q : Subgroup G} (h : P ≤ Q) :
    FixedPoints.subgroup Q V ≤ FixedPoints.subgroup P V := by
  intro v hv p
  exact hv ⟨p,h p.property⟩

private theorem canonical_le (X : Subgroup G)
    (hX : X ∈ smallSupportFactors G V 1) : X ≤ smallSupportGroup G V 1 :=
  le_sSup hX

theorem canonical_fixed_isInvariant :
    IsInvariant G V (FixedPoints.subgroup (smallSupportGroup G V 1) V) := by
  constructor
  intro g v
  constructor
  · intro hv x
    have hmem : g⁻¹ * (x:G) * g ∈ smallSupportGroup G V 1 :=
      by simpa only [inv_inv] using (inferInstance : (smallSupportGroup G V 1).Normal).conj_mem x x.property g⁻¹
    change (x:G) • (g • v) = g • v
    calc
      _ = g • ((g⁻¹ * (x:G) * g) • v) := by simp only [← mul_smul]; congr 1; group
      _ = _ := congrArg (fun w : V => g • w) (hv ⟨_,hmem⟩)
  · intro hv
    have hmem (x : smallSupportGroup G V 1) : g * (x:G) * g⁻¹ ∈ smallSupportGroup G V 1 :=
      (inferInstance : (smallSupportGroup G V 1).Normal).conj_mem x x.property g
    intro x
    have hh := congrArg (fun w : V => g⁻¹ • w) (hv ⟨_,hmem x⟩)
    simpa only [Subgroup.smul_def, ← mul_smul, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, one_smul, mul_one] using hh

private theorem family_fixed_invariant_subgroup (T : Subgroup G) :
    IsInvariant T V (FixedPoints.subgroup (smallSupportGroup G V 1) V) :=
  ⟨fun a v => (canonical_fixed_isInvariant (G:=G) (V:=V)).invariant (a:G) v⟩

variable [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

/-- A transposition exhausts the displacement on the canonical moved space,
so it fixes the canonical fixed complement. -/
theorem fixed_complement_of_transposition (t : G) (ht : IsInvolution t)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 4)
    (hc : IsCompl (commutatorAction (smallSupportGroup G V 1) V)
      (FixedPoints.subgroup (smallSupportGroup G V 1) V))
    (hnorm : ¬ ∀ X ∈ smallSupportFactors G V 1,
      t ∈ Subgroup.normalizer (X : Set G)) :
    ∀ v ∈ FixedPoints.subgroup (smallSupportGroup G V 1) V, t • v = v := by
  obtain ⟨X,Y,_,_,_,_,he⟩ :=
    (smallSupportFactors_normalized_or_single_transposition (V:=V) t ht hcard).resolve_left hnorm
  have hU : commutatorAction X.val V ⊔ commutatorAction Y.val V ≤
      commutatorAction (smallSupportGroup G V 1) V := by
    rw [smallSupportGroup_support_eq_iSup]
    exact sup_le (le_iSup_of_le X le_rfl) (le_iSup_of_le Y le_rfl)
  have hfull : commutatorAction (Subgroup.zpowers t) V ≤
      commutatorAction (smallSupportGroup G V 1) V := by
    rw [he]
    rw [commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨a,v,hv,rfl⟩
    have hi := commutatorAction_isInvariant_of_normalizing_actor
      (V:=V) (Subgroup.zpowers t) (smallSupportGroup G V 1)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    exact (commutatorAction (smallSupportGroup G V 1) V).mul_mem
      ((commutatorAction (smallSupportGroup G V 1) V).inv_mem (hU hv))
      ((hi.invariant a v).mp (hU hv))
  intro v hv
  have hd : v⁻¹ * (t • v) ∈ commutatorAction (Subgroup.zpowers t) V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨t,Subgroup.mem_zpowers t⟩,v,rfl⟩
  have hw : v⁻¹ * (t • v) ∈ FixedPoints.subgroup (smallSupportGroup G V 1) V :=
    (FixedPoints.subgroup _ V).mul_mem ((FixedPoints.subgroup _ V).inv_mem hv)
      ((canonical_fixed_isInvariant (G:=G) (V:=V)).invariant t v |>.mp hv)
  exact (inv_mul_eq_one.mp (hc.disjoint.le_bot ⟨hfull hd,hw⟩)).symm

/-- An inverted canonical plane contributes one displacement dimension. If the
fixed complement is moved, it contributes the other, leaving every other
canonical plane fixed. -/
theorem normalized_inverted_factor_budget
    (t : G) (ht : IsInvolution t)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 4)
    (hnorm : ∀ Z ∈ smallSupportFactors G V 1,
      t ∈ Subgroup.normalizer (Z : Set G))
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V 1)
    (hinv : ∀ x ∈ X, t*x*t⁻¹=x⁻¹)
    (hmove : ∃ v ∈ FixedPoints.subgroup (smallSupportGroup G V 1) V, t • v ≠ v) :
    Nat.card (commutatorSubgroup (Subgroup.zpowers t) V
      (FixedPoints.subgroup (smallSupportGroup G V 1) V)) = 2 ∧
    ∀ Z ∈ smallSupportFactors G V 1, Z ≠ X →
      ∀ v ∈ commutatorAction Z V, t • v = v := by
  let T := Subgroup.zpowers t
  let U := commutatorAction X V
  let W := FixedPoints.subgroup (smallSupportGroup G V 1) V
  let DU := commutatorSubgroup T V U
  let DW := commutatorSubgroup T V W
  let D := commutatorAction T V
  have hdata := invertedOddSubgroup_support_card_data (W:=V) X
    (by rw [hX.2.1]; decide) t ht hinv
  have hDU : Nat.card DU = 2 := by
    have hh : 4 = Nat.card DU ^ 2 := hX.2.2.symm.trans hdata.1
    nlinarith
  have hDUU : DU ≤ U := hdata.2.1
  have hDUD : DU ≤ D := hdata.2.2
  have hDWW : DW ≤ W := displacement_le_support T W (family_fixed_invariant_subgroup T)
  have hDWD : DW ≤ D := displacement_le_full T W
  have hdis : Disjoint U W :=
    (ActionSupport.fixed_support_isCompl X (smallSupportFactor_coprime (Or.inl rfl) hX)).disjoint.symm.mono_right
      (fixed_mono (canonical_le X hX))
  have hcardSup : Nat.card (DU ⊔ DW : Subgroup V) = 2 * Nat.card DW := by
    rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint DU DW
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) (hdis.mono hDUU hDWW), hDU]
  have hsmall : Nat.card DW ≤ 2 := by
    have hb := Subgroup.card_le_of_le (sup_le hDUD hDWD)
    change Nat.card (DU ⊔ DW : Subgroup V) ≤ Nat.card D at hb
    rw [hcardSup, hcard] at hb
    omega
  have hne : Nat.card DW ≠ 1 := by
    intro he
    have hb := Subgroup.card_eq_one.mp he
    obtain ⟨v,hv,hm⟩ := hmove
    have hh : v⁻¹ * (t • v) ∈ DW :=
      Subgroup.subset_closure ⟨⟨t,Subgroup.mem_zpowers t⟩,v,hv,rfl⟩
    rw [hb] at hh
    exact hm (inv_mul_eq_one.mp hh).symm
  have hpos : 0 < Nat.card DW := Nat.card_pos
  have hDW : Nat.card DW = 2 := by omega
  have hsat : DU ⊔ DW = D :=
    Subgroup.eq_of_le_of_card_ge (sup_le hDUD hDWD) (by rw [hcardSup,hDW,hcard])
  refine ⟨hDW,?_⟩
  intro Z hZ hZX v hv
  have hfixed : D ≤ FixedPoints.subgroup Z V := by
    rw [←hsat]
    exact sup_le (hDUU.trans (smallSupportFactors_cross_fixed (Or.inl rfl) hZ hX hZX))
      (hDWW.trans (fixed_mono (canonical_le Z hZ)))
  have hd : v⁻¹ * (t • v) ∈ D := by
    change v⁻¹ * (t • v) ∈ commutatorAction T V
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨t,Subgroup.mem_zpowers t⟩,v,rfl⟩
  have hZstable := commutatorAction_isInvariant_of_normalizing_actor (V:=V) T Z
    (Subgroup.zpowers_le.mpr (hnorm Z hZ))
  have hz : v⁻¹ * (t • v) ∈ commutatorAction Z V :=
    (commutatorAction Z V).mul_mem ((commutatorAction Z V).inv_mem hv)
      ((hZstable.invariant ⟨t,Subgroup.mem_zpowers t⟩ v).mp hv)
  have hc := ActionSupport.fixed_support_isCompl Z (smallSupportFactor_coprime (Or.inl rfl) hZ)
  exact (inv_mul_eq_one.mp (hc.disjoint.le_bot ⟨hfixed hd,hz⟩)).symm
end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree

open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
  [Finite G]

/-- An inverted cubic lies in the same canonical permutation kernel as its
inverting involution. Its odd order then makes it centralize each cubic factor. -/
theorem inverted_cubic_centralizes_factors
    (t x : G) (ht : IsInvolution t) (hx : x^3=1)
    (hinv : t*x*t⁻¹=x⁻¹)
    (hnorm : ∀ P ∈ smallSupportFactors G V 1,
      t ∈ Subgroup.normalizer (P : Set G)) :
    ∀ P ∈ smallSupportFactors G V 1, ∀ p ∈ P, Commute x p := by
  intro P hP
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht.2)
  have htfix (Q : Subgroup G) (hQ : Q ∈ smallSupportFactors G V 1) : Q.conjBy t=Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm Q hQ)
  have he : P.conjBy x⁻¹ = P.conjBy x := by
    rw [←hinv,Subgroup.conjBy_mul,Subgroup.conjBy_mul,hti,htfix P hP,
      htfix (P.conjBy x) (smallSupportFactors_conjBy hP x)]
  have htwo : P.conjBy (x*x)=P := by
    rw [Subgroup.conjBy_mul,←he,Subgroup.conjBy_inv']
  have hn : x ∈ Subgroup.normalizer (P : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    calc
      P.conjBy x = (P.conjBy (x*x)).conjBy x := by rw [htwo]
      _ = P.conjBy (x*(x*x)) := (Subgroup.conjBy_mul _ _ _).symm
      _ = P := by
        have hxxx : x*(x*x)=1 := by simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hx
        rw [hxxx,Subgroup.conjBy_one]
  let φ : MulAut P := P.normalizerMonoidHom ⟨x,hn⟩
  let : IsCyclic P := smallSupportFactor_isCyclic (Or.inl rfl) hP
  have hφ3 : φ^3=1 := by
    change P.normalizerMonoidHom (⟨x,hn⟩:Subgroup.normalizer (P:Set G)) ^ 3=1
    rw [←map_pow,show (⟨x,hn⟩:Subgroup.normalizer (P:Set G))^3=1 from Subtype.ext hx,map_one]
  have hcardAut : Nat.card (MulAut P)=2 := by
    rw [IsCyclic.card_mulAut,hP.2.1]
    decide
  have hd2 : orderOf φ ∣ 2 := hcardAut ▸ orderOf_dvd_natCard φ
  have hd3 : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
  have hφ : φ=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3) hd2 hd3)
  intro p hp
  have heq := congrArg (fun f : MulAut P => (f ⟨p,hp⟩ : G)) hφ
  change x*p*x⁻¹=p at heq
  exact mul_inv_eq_iff_eq_mul.mp heq

end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
