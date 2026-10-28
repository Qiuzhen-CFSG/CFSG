module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneFactorSelection
public import Theory.SpecificGroups.SymmetricThree.NormalInProperSubgroup
public import Theory.Representation.BinaryOffender.SmallMovedInvolutions
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Symmetric-three quotients of rank-one normal closures

A quasisimple B.5.1 actor has a Sylow-two supplement, so its perfect
subgroup and the supplement cannot surject onto S3. In B.5.6's two-factor
and hyperplane rows, a rank-one involution belongs to one original factor.
If it survives in an S3 quotient, the opposite factor is exactly the
quotient kernel. Normality of that kernel in the ambient group makes the
marked factor ambient normal as well, contradicting generation by the
original involution's ambient conjugates.

The hyperplane proof uses the faithful actions on the two disjoint moved
spaces; it does not assume a splitting of the entire module. The kernel's
ambient normality is essential and remains explicit. The actual consumer
is the K-action on VH in original 14.3.25, where both quotients and this
normality are constructed from the original conjugation maps.

Source: Aschbacher--Smith B.5.1, B.5.6(3),(5), and the transvection argument
in 14.3.25, printed pp.99--105 and 1001.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem symmetricThree_not_two : ¬ IsPGroup 2 (Equiv.Perm (Fin 3)) := by
  intro hp
  obtain ⟨n,hn⟩ := hp.exists_card_dvd_pow
  have hd : 3 ∣ 2 ^ n := (show 3 ∣ Nat.card (Equiv.Perm (Fin 3)) from by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]).trans hn
  exact (by decide : ¬ 3 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide)) hd)

/-- The quasisimple B.5.1 row has no symmetric-three quotient. -/
theorem ProjectiveLine.QuasisimpleSourceConclusion.no_symmetricThree_quotient
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) D X} {L : Subgroup D} [Group.IsPerfect L]
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (f : D →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f) : False := by
  let := symmetricThree_solvable
  let r := f.comp L.subtype
  let : Group.IsPerfect r.range := Group.IsPerfect.range r
  have hs : Subsingleton r.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable r.range inferInstance
  have hL : L.map f = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    rintro x ⟨l,hl,rfl⟩
    exact congrArg Subtype.val (Subsingleton.elim (r.rangeRestrict ⟨l,hl⟩) 1)
  have hsup : ∃ S : Sylow 2 D, L ⊔ (S : Subgroup D) = ⊤ := by
    obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := D)
    cases c.clause_one with
    | irreducible _ _ _ _ he =>
      rcases he with ht | ⟨he,_⟩
      · exact ⟨S,by rw [ht,top_sup_eq]⟩
      · exact ⟨S,he S⟩
    | doubleThree _ ht _ _ _ => exact ⟨S,by rw [ht,top_sup_eq]⟩
    | naturalDual _ _ ht _ => exact ⟨S,by rw [ht,top_sup_eq]⟩
    | repeatedNatural _ _ _ _ _ ht _ => exact ⟨S,by rw [ht,top_sup_eq]⟩
  obtain ⟨S,hS⟩ := hsup
  have hmap : (S : Subgroup D).map f = ⊤ := by
    have hh := congrArg (Subgroup.map f) hS
    rwa [Subgroup.map_sup,hL,bot_sup_eq,map_top_of_surjective f hf] at hh
  have hp := S.isPGroup'.map f
  rw [hmap] at hp
  exact symmetricThree_not_two (hp.of_equiv topEquiv)

private theorem factor_quotient_kernel
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) D X}
    (d : SourceTwoFactorCase ρ) (f : D →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (t : D) (ht : t ∈ d.first)
    (ht2 : t ^ 2 = 1) (htf : f t ≠ 1) :
    f.ker = d.second := by
  let : d.first.Normal := d.product.swap.second_normal
  let : d.second.Normal := d.product.second_normal
  let r := f.comp d.first.subtype
  let : r.range.Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance f hf
  have hcore : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three
      (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  have hr : Function.Injective r := by
    rcases normal_hom_injective_or_trivial d.firstCase.normal_quotient_two hcore r with hi | he
    · exact hi
    · exact (htf (congrArg (fun q => q ⟨t,ht⟩) he)).elim
  have hrTop : r.range = ⊤ := by
    by_contra hn
    have hz := SymmetricThree.normal_eq_bot_of_le_proper_with_involution
      (MulEquiv.refl _) r.range r.range hn (f t) ⟨⟨t,ht⟩,rfl⟩
      (orderOf_eq_prime (by rw [←map_pow,ht2,map_one]) htf) le_rfl
    exact htf (hz.le ⟨⟨t,ht⟩,rfl⟩)
  have hB : d.second ≤ f.ker := by
    intro b hb
    have hz : f b ∈ center (Equiv.Perm (Fin 3)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨a,ha⟩ := MonoidHom.range_eq_top.mp hrTop y
      have hc : (b : D) * (a : D) = (a : D) * b :=
        (commutator_eq_bot_iff_le_centralizer.mp d.product.commutator_eq_bot a.property) b hb
      change y * f b = f b * y
      rw [←ha]
      change f (a : D) * f b = f b * f (a : D)
      simpa only [map_mul] using (congrArg f hc).symm
    have hcenter : center (Equiv.Perm (Fin 3)) = ⊥ := by
      apply (eq_bot_iff_forall _).mpr
      exact by decide
    exact hcenter.le hz
  apply le_antisymm ?_ hB
  intro x hx
  obtain ⟨a,b,rfl⟩ := d.product.exists_mul x
  have ha : a = 1 := hr (by
    have hh : f ((a : D) * (b : D)) = 1 := hx
    rw [map_mul,show f (b : D) = 1 from hB b.property,mul_one] at hh
    exact hh.trans r.map_one.symm)
  simpa only [ha,OneMemClass.coe_one,one_mul] using b.property

/-- A rank-one normal closure with an ambient-normal symmetric-three quotient
kernel cannot be a two-factor B.5.6 actor. -/
theorem SourceTwoFactorCase.no_normalClosure_symmetricThree_quotient
    {J X : Type*} [Group J] [Finite J] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (K : Subgroup J) [K.Normal] (a : J) (ha : a ∈ K)
    (hK : K = normalClosure ({a} : Set J)) (ρ : Representation (ZMod 2) K X)
    (d : SourceTwoFactorCase ρ)
    (hcore : pCore 2 K = ⊥)
    (f : K →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hn : (f.ker.map K.subtype).Normal)
    (ha2 : a ^ 2 = 1)
    (hfa : f ⟨a,ha⟩ ≠ 1)
    (hr : Module.finrank (ZMod 2)
      (ρ ⟨a,ha⟩ - LinearMap.id).range ≤ 1) : False := by
  let t : K := ⟨a,ha⟩
  have ht2 : t ^ 2 = 1 := Subtype.ext ha2
  have marked_first (c : SourceTwoFactorCase ρ) (ht : t ∈ c.first) : False := by
    have hk := factor_quotient_kernel c f hf t ht ht2 hfa
    have hsecond : (c.second.map K.subtype).Normal := hk ▸ hn
    have hperm (g : J) : c.first.map (MulAut.conjNormal g).toMonoidHom = c.first := by
      have hB : c.second.map (MulAut.conjNormal g).toMonoidHom = c.second := by
        apply eq_of_le_of_card_ge ?_ (card_map_of_injective
          (f := (MulAut.conjNormal g).toMonoidHom) (MulAut.conjNormal g).injective).ge
        rintro x ⟨b,hb,rfl⟩
        have hm := hsecond.conj_mem (b : J) (mem_map_of_mem K.subtype hb) g
        obtain ⟨z,hz,he⟩ := hm
        have he' : z = MulAut.conjNormal g b := Subtype.ext he
        exact he' ▸ hz
      rcases c.automorphism_permutation hcore (MulAut.conjNormal g) with hh | hh
      · exact hh.1
      · have he : c.first = c.second := hh.2.symm.trans hB
        have ht1 : t = 1 := Subgroup.disjoint_def.mp c.product.disjoint ht (he ▸ ht)
        exact (hfa ((congrArg f ht1).trans f.map_one)).elim
    have hA : (c.first.map K.subtype).Normal := by
      constructor
      rintro x ⟨b,hb,rfl⟩ g
      exact mem_map_of_mem K.subtype ((hperm g).le
        (mem_map_of_mem (MulAut.conjNormal g).toMonoidHom hb))
    have hKA : K ≤ c.first.map K.subtype :=
      hK.le.trans (normalClosure_le_normal (by
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact mem_map_of_mem K.subtype ht))
    have hAall : c.first = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨y,hy,he⟩ := hKA x.property
      exact (Subtype.ext he : y = x) ▸ hy
    have hBbot : c.second = ⊥ := by
      apply le_bot_iff.mp
      intro b hb
      exact Subgroup.disjoint_def.mp c.product.disjoint (hAall ▸ mem_top b) hb
    exact (nontrivial_iff_ne_bot _).mp c.secondCase.nontrivial hBbot
  rcases d.rank_one_mem_factor t hr with ht | ht
  · exact marked_first d ht
  · let ds : SourceTwoFactorCase ρ :=
      ⟨d.second,d.first,d.product.swap,d.secondSpace,d.firstSpace,
        d.decomposition.symm,d.secondCase,d.firstCase⟩
    exact marked_first ds ht

end CFSG.Quasithin.ChapterB.SourceInduction

namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource

private theorem perfect_symmetricThree_trivial {D : Type*} [Group D] [Group.IsPerfect D]
    (f : D →* Equiv.Perm (Fin 3)) : f = 1 := by
  let := symmetricThree_solvable
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  apply MonoidHom.ext
  intro x
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict x) 1)

private theorem center_eq_bot_transport {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (hz : center E = ⊥) : center D = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  apply e.injective
  rw [map_one]
  apply hz.le
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z,rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)

private theorem hyperplane_second_model
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) D X} (c : HyperplaneCase ρ)
    (f : D →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f) :
    Nonempty (c.second ≃* Equiv.Perm (Fin 3)) ∧ f.ker = c.first := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect c.first := Group.IsPerfect.ofSurjective
    (f := c.firstEquiv.symm.toMonoidHom) c.firstEquiv.symm.surjective
  have hfirst (a : c.first) : f (a : D) = 1 :=
    congrArg (fun q : c.first →* Equiv.Perm (Fin 3) => q a)
      (perfect_symmetricThree_trivial (f.comp c.first.subtype))
  let r := f.comp c.second.subtype
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨x,rfl⟩ := hf z
    obtain ⟨a,b,rfl⟩ := c.product.exists_mul x
    refine ⟨b,?_⟩
    simp only [map_mul,hfirst,one_mul]
    rfl
  have he : Nonempty (c.second ≃* Equiv.Perm (Fin 3)) := by
    have nonperfect (h : Group.IsPerfect c.second) : False := by
      let := h
      have hh := perfect_symmetricThree_trivial r
      obtain ⟨z,hz⟩ := exists_ne (1 : Equiv.Perm (Fin 3))
      obtain ⟨b,rfl⟩ := hr z
      exact hz (congrArg (fun q : c.second →* Equiv.Perm (Fin 3) => q b) hh)
    cases c.secondCase with
    | linearThree n hn hm =>
      obtain ⟨e⟩ := hm
      let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) BinaryField.two.Carrier) :=
        Atlas.sl_perfect 3 (by decide)
      exact (nonperfect (Group.IsPerfect.ofSurjective
        (f := e.groupEquiv.symm.toMonoidHom) e.groupEquiv.symm.surjective)).elim
    | linearTwo F hm =>
      obtain ⟨e⟩ := hm
      by_cases hd : F.degree = 1
      · exact ⟨e.groupEquiv.trans
          ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
            ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
              BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))⟩
      · have hlarge : 3 < Nat.card F.Carrier := by
          rw [F.card_eq]
          have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
          have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
          norm_num at hp
          omega
        let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
          GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hlarge
        exact (nonperfect (Group.IsPerfect.ofSurjective
          (f := e.groupEquiv.symm.toMonoidHom) e.groupEquiv.symm.surjective)).elim
  refine ⟨he,?_⟩
  obtain ⟨e⟩ := he
  have hi : Function.Injective r := (hr.bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).le).1
  apply le_antisymm
  · intro x hx
    obtain ⟨a,b,rfl⟩ := c.product.exists_mul x
    have hb : b = 1 := hi (by
      have hh : f ((a : D) * (b : D)) = 1 := hx
      rw [map_mul,hfirst,one_mul] at hh
      exact hh.trans r.map_one.symm)
    simpa only [hb,OneMemClass.coe_one,mul_one] using a.property
  · intro a ha
    exact hfirst ⟨a,ha⟩

private theorem rank_one_in_product_factor
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] (ρ : Representation (ZMod 2) D X)
    (hρ : Function.Injective ρ) (hcore : pCore 2 D = ⊥)
    {A B : Subgroup D} (p : InternalProduct A B)
    (hA : center A = ⊥) (hB : center B = ⊥)
    (hd : Disjoint (moved ρ A) (moved ρ B)) (t : D)
    (hr : Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 1) : t ∈ A ∨ t ∈ B := by
  let : A.Normal := p.swap.second_normal
  let : B.Normal := p.second_normal
  let movedRep (N : Subgroup D) [N.Normal] : Subrepresentation ρ :=
    ⟨moved ρ N, fun g v hv =>
      (subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
        (show (⊤ : Subgroup D) ≤ normalizer (N : Set D) from le_normalizer_of_normal)
        (mem_top g) v).2 hv⟩
  let U := movedRep A
  let W := movedRep B
  have hUA : Function.Injective (U.toRepresentation.comp A.subtype) :=
    faithful_on_moved_subrepresentation ρ hρ A (p.swap.second_twoCore hcore) U rfl
  have hWB : Function.Injective (W.toRepresentation.comp B.subtype) :=
    faithful_on_moved_subrepresentation ρ hρ B (p.second_twoCore hcore) W rfl
  let δ := ρ t - LinearMap.id
  have hinv (S : Subrepresentation ρ) : S.toSubmodule.map δ ≤ S.toSubmodule := by
    rintro _ ⟨v,hv,rfl⟩
    exact S.toSubmodule.sub_mem (S.apply_mem_toSubmodule t hv) hv
  have hk (S : Subrepresentation ρ) (hs : S.toSubmodule ≤ δ.ker) : t ∈ S.toRepresentation.ker := by
    apply MonoidHom.mem_ker.mpr
    ext v
    exact sub_eq_zero.mp (hs v.property)
  have hdis (N : Subgroup D) (S : Subrepresentation ρ)
      (hf : Function.Injective (S.toRepresentation.comp N.subtype)) :
      Disjoint S.toRepresentation.ker N := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hxN
    have he : (⟨x,hxN⟩ : N) = 1 := hf (by
      change S.toRepresentation x = S.toRepresentation 1
      rw [map_one]
      exact hx)
    exact congrArg Subtype.val he
  rcases LinearMap.invariant_disjoint_pair_rank_one δ hr U.toSubmodule W.toSubmodule
    hd (hinv U) (hinv W) with hu | hw
  · exact Or.inr (p.normal_disjoint_first_le_second hA U.toRepresentation.ker
      (hdis A U hUA) (hk U hu))
  · exact Or.inl (p.swap.normal_disjoint_first_le_second hB W.toRepresentation.ker
      (hdis B W hWB) (hk W hw))

/-- The hyperplane B.5 row cannot be a rank-one normal closure with an
ambient-normal symmetric-three quotient kernel. -/
theorem HyperplaneCase.no_normalClosure_symmetricThree_quotient
    {J X : Type*} [Group J] [Finite J] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (K : Subgroup J) [K.Normal] (a : J) (ha : a ∈ K)
    (hK : K = normalClosure ({a} : Set J)) (ρ : Representation (ZMod 2) K X)
    (c : HyperplaneCase ρ) (hρ : Function.Injective ρ) (hcore : pCore 2 K = ⊥)
    (f : K →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hn : (f.ker.map K.subtype).Normal) (hfa : f ⟨a,ha⟩ ≠ 1)
    (hr : Module.finrank (ZMod 2) (ρ ⟨a,ha⟩ - LinearMap.id).range ≤ 1) : False := by
  obtain ⟨⟨e⟩,hk⟩ := hyperplane_second_model c f hf
  have hfirst : center c.first = ⊥ := center_eq_bot_transport c.firstEquiv
    (Matrix.PSL3.OddDegreeProjectiveComparison.center_eq_bot (n := 1) (by simp) (by decide))
  have hsecond : center c.second = ⊥ := center_eq_bot_transport e (by
    apply (eq_bot_iff_forall _).mpr
    exact by decide)
  let t : K := ⟨a,ha⟩
  have ht : t ∈ c.second := by
    rcases rank_one_in_product_factor ρ hρ hcore c.product hfirst hsecond c.disjoint t hr with ht | ht
    · exact (hfa (show t ∈ f.ker from hk.symm ▸ ht)).elim
    · exact ht
  have hN : (c.first.map K.subtype).Normal := hk ▸ hn
  have hB : (c.second.map K.subtype).Normal := by
    have he : c.second.map K.subtype = K ⊓ centralizer (c.first.map K.subtype : Set J) := by
      apply le_antisymm
      · rintro x ⟨b,hb,rfl⟩
        refine ⟨b.property,?_⟩
        apply mem_centralizer_iff.mpr
        rintro z ⟨w,hw,rfl⟩
        exact congrArg Subtype.val
          (mem_centralizer_iff.mp ((c.product.centralizer_first_eq_second hfirst).symm ▸ hb) w hw)
      · rintro x ⟨hx,hxc⟩
        refine ⟨⟨x,hx⟩,?_,rfl⟩
        rw [← c.product.centralizer_first_eq_second hfirst]
        apply mem_centralizer_iff.mpr
        intro y hy
        exact Subtype.ext (mem_centralizer_iff.mp hxc y (mem_map_of_mem K.subtype hy))
    rw [he]
    let := hN
    infer_instance
  have hKB : K ≤ c.second.map K.subtype := hK.le.trans (normalClosure_le_normal (by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact mem_map_of_mem K.subtype ht))
  have hBtop : c.second = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y,hy,he⟩ := hKB x.property
    exact (Subtype.ext he : y = x) ▸ hy
  have hAbot : c.first = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.disjoint_def.mp c.product.disjoint hx (hBtop ▸ mem_top x)
  have hd := c.firstDimension
  rw [hAbot] at hd
  have hz : moved ρ (⊥ : Subgroup K) = ⊥ := by
    apply le_bot_iff.mp
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,v,_,rfl⟩
    have hx1 : x = 1 := hx
    simp only [hx1,map_one,Module.End.one_apply,sub_self]
    exact Submodule.zero_mem _
  rw [hz,finrank_bot] at hd
  omega

end CFSG.Quasithin.ChapterB.SourceInduction
