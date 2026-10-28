module
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.SpecificGroups.PSL2.PrimeCartanNormalizer
public import Theory.GroupTheory.SolvableSylowOvergroups.OddActors

/-!
# Solvable odd-prime PSL₂ subgroups containing A₄

Dickson's cyclic, dihedral and odd-by-cyclic rows cannot contain A₄:
two-perfectness places a dihedral image in the rotations, and a normal
four-group cannot embed in an odd-by-cyclic group. The remaining solvable
rows are A₄ and S₄, whose orders are prime to five.

For a normal subgroup with an actual odd-prime PSL₂ marking, the outer
group is a two-group. A faithful quintic actor therefore has an inner
image. Pulling a solvable ambient join back through conjugation retains
its embedded A₄, so the intrinsic calculation excludes the actor.

Source: Huppert II.8.27 (Dickson), used in Aschbacher–Smith 5.1.13 and
5.2.2, printed pp.636–638,648–649. The Chapter6 prime-field extension
applies this to the literal selected right Borel and escaping actor.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped Pointwise
public noncomputable section
namespace Theory.PSL2.PrimeFourSolvable
local notation "A4" => alternatingGroup (Fin 4)
private theorem a4_twoPerfect : IsPPerfect 2 A4 := by
  rw [← Equiv.Perm.twoResidual_eq_alternating]
  exact isPPerfect_pResidual 2
private theorem a4_not_cyclic : ¬ IsCyclic A4 := by
  intro hc
  let := hc
  let : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
    alternatingGroup.kleinFour_isKleinFour (by simp)
  exact IsKleinFour.not_isCyclic (G := alternatingGroup.kleinFour (Fin 4)) inferInstance

private theorem no_dihedral_embedding {n : ℕ} (f : A4 →* DihedralGroup n)
    (hi : Function.Injective f) : False := by
  let r : Multiplicative (ZMod n) →* DihedralGroup n := {
    toFun i := DihedralGroup.r i.toAdd
    map_one' := DihedralGroup.r_zero
    map_mul' i j := by simp }
  let parity : DihedralGroup n →* Multiplicative (ZMod 2) := {
    toFun
      | DihedralGroup.r _ => 1
      | DihedralGroup.sr _ => Multiplicative.ofAdd 1
    map_one' := rfl
    map_mul' a b := by
      cases a <;> cases b <;> simp
      change (0 : ZMod 2) = 1 + 1
      exact (ZMod.natCast_self 2).symm }
  have hzero := a4_twoPerfect.hom_eq_one_of_isPGroup
    (IsPGroup.of_card (p := 2) (n := 1) (by simp)) (parity.comp f)
  have hr (a : A4) : f a ∈ r.range := by
    have he := DFunLike.congr_fun hzero a
    cases hx : f a with
    | r i => exact ⟨Multiplicative.ofAdd i,rfl⟩
    | sr i =>
      change parity (f a) = 1 at he
      rw [hx] at he
      change Multiplicative.ofAdd (1 : ZMod 2) = 1 at he
      have hh := congrArg Multiplicative.toAdd he
      norm_num at hh
  let : IsCyclic r.range := isCyclic_of_surjective r.rangeRestrict r.rangeRestrict_surjective
  exact a4_not_cyclic (isCyclic_of_injective (f.codRestrict r.range hr)
    (fun _ _ h => hi (congrArg Subtype.val h)))

private theorem no_odd_cyclic_embedding {Y : Type*} [_root_.Group Y] [Finite Y]
    (N C : Subgroup Y) [N.Normal] [IsCyclic C]
    (hN : Odd (Nat.card N)) (hdis : Disjoint N C) (hsup : N ⊔ C = ⊤)
    (f : A4 →* Y) (hi : Function.Injective f) : False := by
  let : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
    alternatingGroup.kleinFour_isKleinFour (by simp)
  let V := alternatingGroup.kleinFour (Fin 4)
  have hcomp : N.IsComplement' C := by
    refine ⟨mul_injective_of_disjoint hdis,?_⟩
    intro g
    have hg : g ∈ (N : Set Y) * (C : Set Y) := by
      rw [←normal_mul N C,hsup]; trivial
    obtain ⟨n,hn,c,hc,he⟩ := hg
    exact ⟨⟨⟨n,hn⟩,⟨c,hc⟩⟩,he⟩
  let : IsCyclic (Y ⧸ N) := hcomp.symm.QuotientMulEquiv.isCyclic.mpr inferInstance
  let j : V →* Y := f.comp V.subtype
  have hj : Function.Injective j := hi.comp V.subtype_injective
  have hd : Disjoint j.range N := disjoint_of_coprime_natCard (by
    rw [←Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,IsKleinFour.card_four]
    exact hN.coprime_two_left.pow_left 2)
  let q : V →* Y ⧸ N := (QuotientGroup.mk' N).comp j
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro v hv
    apply hj
    rw [map_one]
    exact mem_bot.mp (hd.le_bot ⟨⟨v,rfl⟩,(QuotientGroup.eq_one_iff _).mp hv⟩)
  exact IsKleinFour.not_isCyclic (G := V) (isCyclic_of_injective q hq)

/-- A solvable subgroup of odd prime-field PSL₂ containing A₄ is prime to five. -/
theorem not_five_of_alternating_four
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (H : Subgroup (PSL2MatrixGroup F)) [_root_.Group.IsSolvable H]
    (f : A4 →* H) (hi : Function.Injective f) : ¬ 5 ∣ Nat.card H := by
  have hcardF : Nat.card F = p ^ 1 := by simpa using hF
  intro h5
  have h4 : 4 ∣ Nat.card H := by
    have hd := card_dvd_of_injective f hi
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact (by decide : 4 ∣ 12).trans hd
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hcardF H with hEl | hCy | hDi | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    exact (ha ▸ ho.pow).not_two_dvd_nat ((by decide : 2 ∣ 4).trans h4)
  · let : IsCyclic H := hCy.choose_spec.2.2
    exact a4_not_cyclic (isCyclic_of_injective f hi)
  · obtain ⟨_,_,_,⟨e⟩⟩ := hDi
    exact no_dihedral_embedding (e.toMonoidHom.comp f) (e.injective.comp hi)
  · obtain ⟨_,⟨e⟩⟩ := hA4
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at h5
    norm_num [Nat.factorial] at h5
  · obtain ⟨_,⟨e⟩⟩ := hS4
    rw [Nat.card_congr e.toEquiv,Nat.card_perm] at h5
    norm_num [Nat.factorial] at h5
  · obtain ⟨_,⟨e⟩⟩ := hA5
    let : _root_.Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact _root_.Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
      (_root_.Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨a,t,_,_,N,C,hN,_,hcN,hC,_,hd,hs⟩ := hAff
    let := hN
    let := hC
    exact no_odd_cyclic_embedding N C (by rw [hcN]; exact ho.pow) hd hs f hi
  · obtain ⟨a,ha,had,⟨e⟩⟩ := hPSL
    have he : a = 1 := Nat.eq_one_of_dvd_one had
    subst a
    have hc : Nat.card (GaloisField p 1) = p := by simpa using GaloisField.card p 1 (by decide)
    let : _root_.Group.IsPerfect (PSL2MatrixGroup (GaloisField p 1)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by rw [hc]; exact hp)
    exact _root_.Group.IsPerfect.not_isSolvable (PSL2MatrixGroup (GaloisField p 1))
      (_root_.Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨a,ha,had,_⟩ := hPGL
    have := Nat.le_of_dvd (by decide : 0 < 1) had
    omega

/-- A faithful quintic actor is impossible in a solvable subgroup containing
an actual A₄ inside a normal odd-prime PSL₂ component. -/
theorem no_five_actor
    {G : Type*} [_root_.Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (K E Y : Subgroup G) [K.Normal] (e : K ≃* PSL2MatrixGroup F)
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hEY : E ≤ Y) [_root_.Group.IsSolvable Y]
    (a : A4 →* K) (ha : Function.Injective a) (hY : ∀ x, (a x : G) ∈ Y) : False := by
  obtain ⟨hz,hout⟩ := primeField_center_outer_of_equiv (Fact.out : p.Prime) ho hF e
  let f : G →* MulAut K := MulAut.conjNormal
  let i : K →* MulAut K := MulAut.conj
  have hi : Function.Injective i := conj_injective_of_center_eq_bot hz
  have hfi (k : K) : f k = i k := by ext x; rfl
  have hEin : E.map f ≤ MulAut.innerSubgroup K := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup K)
    have h5 := ((IsPGroup.of_card (p := 5) (n := 1) (by simpa using hE)).map f).map q
    have h2 := hout.to_subgroup ((E.map f).map q)
    have hb : (E.map f).map q = ⊥ := disjoint_self.mp (h5.disjoint_of_coprime h2 (by decide))
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff (E.map f)).mp hb
  let ec : K ≃* MulAut.innerSubgroup K := MonoidHom.ofInjective hi
  let b : E →* MulAut.innerSubgroup K := (f.comp E.subtype).codRestrict _
    (fun x => hEin (mem_map_of_mem f x.property))
  let g : E →* K := ec.symm.toMonoidHom.comp b
  have hg (x : E) : i (g x) = f x := congrArg Subtype.val (ec.apply_symm_apply (b x))
  have hgi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hfx : f x = 1 := by rw [←hg x,show g x = 1 from hx,map_one]
    have hxC : (x : G) ∈ centralizer (K : Set G) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer]; exact hfx
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨x.property,hxC⟩))
  let J := Y.map f
  let M := J.comap i
  let : _root_.Group.IsSolvable J := _root_.Group.isSolvable_of_surjective (f.subgroupMap_surjective Y)
  let : _root_.Group.IsSolvable M := _root_.Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap J) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  have hM (x : A4) : a x ∈ M := by
    change i (a x) ∈ J
    rw [←hfi]
    exact mem_map_of_mem f (hY x)
  have hr : g.range ≤ M := by
    rintro _ ⟨x,rfl⟩
    change i (g x) ∈ J
    rw [hg]
    exact mem_map_of_mem f (hEY x.property)
  have hc : Nat.card g.range = 5 :=
    (Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv).symm.trans hE
  let eM := M.equivMapOfInjective e.toMonoidHom e.injective
  let : _root_.Group.IsSolvable (M.map e.toMonoidHom) :=
    _root_.Group.isSolvable_of_surjective (f := eM.toMonoidHom) eM.surjective
  have hnot := not_five_of_alternating_four ho hp hF (M.map e.toMonoidHom)
    (eM.toMonoidHom.comp (a.codRestrict M hM))
    (eM.injective.comp (fun _ _ he => ha (congrArg Subtype.val he)))
  rw [card_map_of_injective e.injective] at hnot
  exact hnot (hc ▸ card_dvd_of_le hr)
end Theory.PSL2.PrimeFourSolvable
