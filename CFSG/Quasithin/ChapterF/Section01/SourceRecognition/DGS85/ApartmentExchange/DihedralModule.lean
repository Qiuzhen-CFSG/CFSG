module
public import Theory.GroupAction.InvertedSummands
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic.Ring

/-!
# The dihedral module step of DGS Chapter 14

This proves (14.16) for the original actor, its actual derived subgroup,
and the given reflected summand. A marked dihedral isomorphism identifies
the derived subgroup with the rotations when the rotation order is odd.
The binary inverse-action calculation then forces rotation order three if
a third invariant subgroup of the prescribed order exists. The order-six
exception is retained. The zero module is handled separately; finiteness
of a nonzero summand follows from transitivity of the finite actor.

The final theorem supplies the local use in (14.17), printed p.222:
disjointness from the reflected summand selects the original one. It does
not construct the r=6 local profile, its quotient module, or its compatible
reflections. These remain necessary before applying this module to finish
the original apartment exchange argument. The corrected (14.14), other
profile branches and the TYPE2F4(2) alternative of (14.19) remain separate.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(14.16)--(14.17), printed pp.220--222.
-/

public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open DihedralGroup
open scoped commutatorElement

private def rotations (n : ℕ) : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun a := r a.toAdd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] private lemma rotations_apply (n : ℕ) (a : Multiplicative (ZMod n)) :
    rotations n a=r a.toAdd := rfl

private lemma rotations_injective (n : ℕ) : Function.Injective (rotations n) := by
  intro a b h
  exact congrArg Multiplicative.ofAdd (r.inj h)

private lemma rotations_range_eq_commutator {n : ℕ} (hn : Odd n) :
    (rotations n).range = commutator (DihedralGroup n) := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    obtain ⟨k,hk⟩ := hn
    let j : ZMod n := (k+1)*a.toAdd
    have he : 2*j=a.toAdd := by
      have hcast : (2:ZMod n)*k+1=0 := by
        have hc : (n : ZMod n)=0 := ZMod.natCast_self n
        have hc' : ((2*k+1:ℕ):ZMod n)=0 := by rw [←hk]; exact hc
        simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hc'
      calc
        2*j = ((2:ZMod n)*k+1+1)*a.toAdd := by dsimp [j]; ring
        _ = a.toAdd := by rw [hcast]; ring
    have hh := Subgroup.commutator_mem_commutator
      (show r j ∈ (⊤ : Subgroup (DihedralGroup n)) from trivial)
      (show sr 0 ∈ (⊤ : Subgroup (DihedralGroup n)) from trivial)
    change _ ∈ commutator (DihedralGroup n) at hh
    have hh' : ⁅r j,sr 0⁆ = r a.toAdd := by
      simp only [commutatorElement_def,r_mul_sr,zero_sub,inv_r,sr_mul_r,inv_sr,sr_mul_sr]
      congr 1
      calc
        _ = 2*j := by ring
        _ = a.toAdd := he
    rw [hh'] at hh
    exact hh
  · rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    rintro (a|a) _ (b|b) _ <;>
      simp only [commutatorElement_def,r_mul_r,r_mul_sr,sr_mul_r,sr_mul_sr,inv_r,inv_sr] <;>
      exact ⟨Multiplicative.ofAdd _,rfl⟩

private lemma reflection_inverts_rotations (n : ℕ) (j : ZMod n)
    (a : Multiplicative (ZMod n)) :
    sr j * rotations n a * (sr j)⁻¹ = rotations n a⁻¹ := by
  change sr j * r a.toAdd * (sr j)⁻¹ = r (-a.toAdd)
  simp

/-- DGS (14.16): in a binary dihedral module split into two reflected regular
summands, only those summands have the given order, unless the actor has order six. -/
theorem source_dihedral_module_subgroups
    {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    [DistribMulAction X V] {n:ℕ} (hn : Odd n) (hne : n≠1)
    (e : X ≃* DihedralGroup n) (t:X) (ht:t∉commutator X)
    (U:AddSubgroup V)
    (hU : ∀ a∈commutator X, ∀ v∈U, a•v∈U)
    (hfree : ∀ a∈commutator X, ∀ v∈U, v≠0 → a•v=v → a=1)
    (htrans : ∀ v∈U, ∀ w∈U, v≠0 → w≠0 → ∃ a∈commutator X, a•v=w)
    (hcompl : IsCompl U (U.map (DistribSMul.toAddMonoidHom V t))) :
    Nat.card X=6 ∨ ∀ E:AddSubgroup V,
      (∀ a∈commutator X, ∀ v∈E, a•v∈E) → Nat.card E=Nat.card U →
      E=U ∨ E=U.map (DistribSMul.toAddMonoidHom V t) := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  let : Finite X := Finite.of_equiv (DihedralGroup n) e.symm.toEquiv
  by_cases h6 : Nat.card X=6
  · exact Or.inl h6
  right
  intro E hE hcard
  cases subsingleton_or_nontrivial U with
  | inl hzero =>
    let := hzero
    have hc : Nat.card U=1 := Nat.card_unique
    have hUb : (⊥ : AddSubgroup V)=U :=
      AddSubgroup.eq_of_le_of_card_ge bot_le (by rw [hc]; simp)
    have hEb : (⊥ : AddSubgroup V)=E := by
      have hf : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard,hc]; decide)
      exact AddSubgroup.eq_of_le_of_card_ge bot_le (by rw [hcard,hc]; simp)
    exact Or.inl (hEb.symm.trans hUb)
  | inr hnontrivial =>
    let := hnontrivial
    obtain ⟨u,hu⟩ := exists_ne (0:U)
    let f : Option (commutator X) → U := fun a => match a with
      | none => 0
      | some a => ⟨a.val • u.val,hU a.val a.property u.val u.property⟩
    have hfs : Function.Surjective f := by
      intro v
      by_cases hv : v=0
      · exact ⟨none,hv.symm⟩
      obtain ⟨a,ha,hav⟩ := htrans u.val u.property v.val v.property
        (fun hh => hu (Subtype.ext hh)) (fun hh => hv (Subtype.ext hh))
      exact ⟨some ⟨a,ha⟩,Subtype.ext hav⟩
    let : Finite U := Finite.of_surjective f hfs
    let ι : Multiplicative (ZMod n) →* X := e.symm.toMonoidHom.comp (rotations n)
    have hir : ι.range=commutator X := by
      rw [MonoidHom.range_comp, rotations_range_eq_commutator hn, map_commutator_eq,
        MonoidHom.range_eq_top.mpr e.symm.surjective, ←commutator_def]
    have hii : Function.Injective ι := e.symm.injective.comp (rotations_injective n)
    have hmem (a:Multiplicative (ZMod n)) : ι a∈commutator X :=
      hir ▸ (show ι a∈ι.range from ⟨a,rfl⟩)
    obtain ⟨j,hj⟩ : ∃ j, e t=sr j := by
      cases he : e t with
      | r a =>
        exfalso
        apply ht
        have he' : t=ι (Multiplicative.ofAdd a) := e.injective (by change e t=e (e.symm (r a)); rw [e.apply_symm_apply]; exact he)
        rw [he']
        exact hmem _
      | sr j => exact ⟨j,rfl⟩
    have hi (a:Multiplicative (ZMod n)) : t*ι a*t⁻¹=ι a⁻¹ := by
      apply e.injective
      simpa only [ι,map_mul,map_inv,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply,hj] using reflection_inverts_rotations n j a
    have ht2 (v:V) : v+v=0 := by
      calc
        v+v = (1+1:ZMod 2) • v := by rw [add_smul,one_smul]
        _ = 0 := by rw [show (1+1:ZMod 2)=0 from rfl,zero_smul]
    rcases Theory.GroupAction.invariant_summand_eq_or_cubic ι t U ht2
      (fun a v hv => hU (ι a) (hmem a) v hv) hi
      (fun a v hv hv0 he => hii (by simpa using hfree (ι a) (hmem a) v hv hv0 he))
      (fun v w hv hw hv0 hw0 => by
        obtain ⟨a,ha,he⟩ := htrans v hv w hw hv0 hw0
        rw [←hir] at ha
        obtain ⟨a,rfl⟩ := ha
        exact ⟨a,he⟩)
      hcompl E hcard (fun a v hv => hE (ι a) (hmem a) v hv) with h | h | hc
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hg : (r 1 : DihedralGroup n)^3=1 := by
        have hh := congrArg (rotations n) (hc (Multiplicative.ofAdd (1:ZMod n)))
        simpa only [map_pow,map_one,rotations_apply,toAdd_ofAdd] using hh
      have hd : n∣3 := by
        simpa only [DihedralGroup.orderOf_r_one] using orderOf_dvd_of_pow_eq_one hg
      have hn3 : n=3 := ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hne
      apply h6
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card,hn3]

/-- The local use of (14.16) in (14.17): disjointness from the reflected
summand selects the original summand, provided the dihedral actor is not S₃. -/
theorem source_dihedral_invariant_complement_eq
    {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    [DistribMulAction X V] {n:ℕ} (hn : Odd n) (hne : n≠1)
    (e : X ≃* DihedralGroup n) (t:X) (ht:t∉commutator X)
    (U:AddSubgroup V)
    (hU : ∀ a∈commutator X, ∀ v∈U, a•v∈U)
    (hfree : ∀ a∈commutator X, ∀ v∈U, v≠0 → a•v=v → a=1)
    (htrans : ∀ v∈U, ∀ w∈U, v≠0 → w≠0 → ∃ a∈commutator X, a•v=w)
    (hcompl : IsCompl U (U.map (DistribSMul.toAddMonoidHom V t)))
    (h6 : Nat.card X≠6) (E:AddSubgroup V)
    (hE : ∀ a∈commutator X, ∀ v∈E, a•v∈E) (hcard : Nat.card E=Nat.card U)
    (hdisj : Disjoint E (U.map (DistribSMul.toAddMonoidHom V t))) : E=U := by
  have h := (source_dihedral_module_subgroups hn hne e t ht U hU hfree htrans hcompl).resolve_left h6
  rcases h E hE hcard with he | he
  · exact he
  · have hW : U.map (DistribSMul.toAddMonoidHom V t)=⊥ := by
      rw [he] at hdisj
      exact disjoint_self.mp hdisj
    have hUb : U=⊥ := by
      apply le_bot_iff.mp
      intro v hv
      have hh : t•v=0 := by
        have hh : t•v∈U.map (DistribSMul.toAddMonoidHom V t) := ⟨v,hv,rfl⟩
        rwa [hW,AddSubgroup.mem_bot] at hh
      change v=0
      exact (smul_left_cancel_iff t).mp (hh.trans (smul_zero t).symm)
    exact he.trans (hW.trans hUb.symm)
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
