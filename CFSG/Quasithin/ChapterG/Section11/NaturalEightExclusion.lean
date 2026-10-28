module
public import CFSG.Quasithin.ChapterG.Section11.NaturalExclusion
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PrimeRankZero

/-!
# Excluding the doubled natural A₈ row

The actual centralizer of a normal doubled natural A₆, A₇ or A₈ action
embeds in S₃. Since the original group has trivial two-core, an even
centralizer would be S₃. Its transposition moves the normal three-core
but centralizes the original alternating subgroup, whose three-rank is
two. A.1.31(1), applied to the actual SQTK cover, excludes this.

The centralizer is therefore odd. For A₈, conjugation embeds the quotient
in Aut(A₈) = S₈, whose two-rank is four. G.10.2 then contradicts dimension
twelve. The proper marked reduction retains only doubled natural A₆,
with odd centralizer; the other genuine source branches remain explicit.
No whole-group tensor recognition is asserted from a constituent image.

Source: Aschbacher--Smith A.1.31(1), G.10.2 and G.11.7--8,
printed pp.27--28,357,366--368. The S₈ rank bound follows by its parity
embedding in A₁₀ and GLS volume 3, Proposition 5.2.10(a).
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11

private theorem odd_centralizer_of_symmetric_three_embedding
    {G : Type*} [Group G] [Finite G]
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hc : pCore 2 G = ⊥) (H : Subgroup G) [H.Normal]
    (hr : 2 ≤ primeRank 3 H)
    (j : centralizer (H : Set G) →* Equiv.Perm (Fin 3))
    (hj : Function.Injective j) : Odd (Nat.card (centralizer (H : Set G))) := by
  classical
  let C := centralizer (H : Set G)
  have hcC : pCore 2 C = ⊥ := by
    apply ((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp
    apply bot_unique
    rw [← hc]
    exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map _⟩
  have hd : Nat.card C ∣ 6 := by
    simpa only [Nat.card_perm,Nat.card_fin,show Nat.factorial 3 = 6 from rfl] using
      Subgroup.card_dvd_of_injective j hj
  by_contra ho
  have htwo : 2 ∣ Nat.card C := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
  have hC6 : Nat.card C = 6 := by
    have hlist : Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 3 ∨ Nat.card C = 6 := by
      have hh := Nat.mem_divisors.mpr ⟨hd,(by decide : 6 ≠ 0)⟩
      rw [show Nat.divisors 6 = {1,2,3,6} by decide] at hh
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
    rcases hlist with h | h | h | h
    · omega
    · have hP : IsPGroup 2 C := IsPGroup.of_card (n := 1) (by simpa using h)
      have ht : pCore 2 C = ⊤ := top_unique (le_sSup ⟨inferInstance,hP.to_subgroup ⊤⟩)
      have he : Nat.card C = 1 := by
        have hh := congrArg (fun Q : Subgroup C => Nat.card Q) (hcC.symm.trans ht)
        simpa only [card_bot,card_top] using hh.symm
      omega
    · omega
    · exact h
  let e : C ≃* Equiv.Perm (Fin 3) := MulEquiv.ofBijective j
    (hj.bijective_of_nat_card_le (by
      change Nat.card (Equiv.Perm (Fin 3)) ≤ Nat.card C
      rw [hC6]
      rw [Nat.card_perm,Nat.card_fin]
      decide))
  let Q : Subgroup C := (alternatingGroup (Fin 3)).comap e.toMonoidHom
  have hQ : IsPGroup 3 Q := by
    have hA : IsPGroup 3 (alternatingGroup (Fin 3)) := by
      apply IsPGroup.of_card (n := 1)
      rw [nat_card_alternatingGroup]
      norm_num
    exact hA.comap_of_injective e.toMonoidHom e.injective
  have hQP : Q ≤ pCore 3 C := le_sSup ⟨inferInstance,hQ⟩
  let P : Subgroup G := (pCore 3 C).map C.subtype
  let : P.Normal := ConjAct.normal_of_characteristic_of_normal
  let t : C := e.symm (Equiv.swap 0 1)
  have htC : orderOf t = 2 := by
    rw [← e.orderOf_eq t,e.apply_symm_apply]
    apply orderOf_eq_prime (p := 2) <;> decide
  have ht : orderOf (t : G) = 2 :=
    (orderOf_injective C.subtype C.subtype_injective t).trans htC
  have htP : (t : G) ∉ centralizer (P : Set G) := by
    intro hmem
    let c : C := e.symm (Equiv.swap 0 1 * Equiv.swap 1 2)
    have hcQ : c ∈ Q := by
      change e (e.symm _) ∈ alternatingGroup (Fin 3)
      rw [e.apply_symm_apply,Equiv.Perm.mem_alternatingGroup]
      decide
    have hcP : (c : G) ∈ P := mem_map_of_mem C.subtype (hQP hcQ)
    have he : c * t = t * c := Subtype.ext (mem_centralizer_iff.mp hmem c hcP)
    have he' := congrArg e he
    simp only [map_mul, c, t, e.apply_symm_apply] at he'
    exact (by decide :
      (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) * Equiv.swap 0 1 ≠
        Equiv.swap 0 1 * (Equiv.swap 0 1 * Equiv.swap 1 2)) he'
  obtain ⟨s⟩ := cover
  have hbound := primeRank_involutionCentralizer_le_one_of_surjective_rank_le_two
    (by decide : Odd 3) s.projection s.surjective
    (s.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    P (pCore_isPGroup.map C.subtype) (t : G) ht htP
  have hH : H ≤ centralizer ({(t : G)} : Set G) := by
    intro x hx y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact (mem_centralizer_iff.mp t.property x hx).symm
  have hle := (primeRank_mono 3 hH).trans hbound
  omega

private def signPair : ℤˣ →* Equiv.Perm (Fin 2) where
  toFun u := if u = 1 then 1 else Equiv.swap 0 1
  map_one' := by simp
  map_mul' a b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> decide
private theorem sign_signPair (u : ℤˣ) : Equiv.Perm.sign (signPair u) = u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide
private def evenExtension : Equiv.Perm (Fin 8) →* alternatingGroup (Fin 8 ⊕ Fin 2) :=
  ((Equiv.Perm.sumCongrHom (Fin 8) (Fin 2)).comp
    ((MonoidHom.id _).prod (signPair.comp Equiv.Perm.sign))).codRestrict _ (by
      intro g
      change Equiv.Perm.sign (Equiv.sumCongr g (signPair (Equiv.Perm.sign g))) = 1
      rw [Equiv.Perm.sign_sumCongr,sign_signPair]
      simpa only [pow_two] using Int.units_sq (Equiv.Perm.sign g))
private theorem evenExtension_injective : Function.Injective evenExtension := by
  intro a b hab
  have hp := Equiv.Perm.sumCongrHom_injective (congrArg Subtype.val hab)
  exact congrArg Prod.fst hp
private theorem symmetric_eight_two_rank : primeRank 2 (Equiv.Perm (Fin 8)) ≤ 4 := by
  let e := Equiv.altCongrHom (finSumFinEquiv : Fin 8 ⊕ Fin 2 ≃ Fin 10)
  let j := e.toMonoidHom.comp evenExtension
  have hj : Function.Injective j := e.injective.comp evenExtension_injective
  have hA := (GLS3.Chapter5.PRank.alternating_hasPRank_two 10).primeRank_eq Nat.prime_two
  exact (_root_.primeRank_le_of_injective 2 j hj).trans (by simpa using hA.le)
private theorem alternating_eight_automorphism_two_rank :
    primeRank 2 (MulAut (alternatingGroup (Fin 8))) ≤ 4 := by
  let e : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      8 (by decide) (by decide))
  exact (_root_.primeRank_le_of_injective 2 e.symm.toMonoidHom e.symm.injective).trans
    symmetric_eight_two_rank

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The original centralizer is odd for each of the doubled natural
A₆, A₇ and A₈ rows. The rank hypothesis is used on the SQTK cover,
not asserted for its arbitrary quotient. -/
theorem natural_centralizer_odd (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (H : Subgroup G) [H.Normal] (n : ℕ)
    (hmodel : Section09.Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n))))
    (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    Odd (Nat.card (centralizer (H : Set G))) := by
  obtain ⟨j,hj⟩ := natural_centralizer_embedding ρ h.faithful H n hmodel hn
  obtain ⟨e,_,_⟩ := hmodel
  apply odd_centralizer_of_symmetric_three_embedding cover h.twoCore_eq_bot H _ j hj
  have hr := _root_.primeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective
  rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n 3 Nat.prime_three (by decide)] at hr
  rcases hn with rfl | rfl | rfl <;> simpa using hr

/-- With the source SQTK cover the doubled natural A₈ centralizer is odd;
conjugation on A₈ therefore bounds the whole group's two-rank by four. -/
theorem doubled_eight_ambient_two_rank (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (H : Subgroup G) [H.Normal]
    (hmodel : Section09.Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 8)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)))) :
    primeRank 2 G ≤ 4 := by
  have ho := natural_centralizer_odd h cover H 8 hmodel (by simp)
  have hC : primeRank 2 (centralizer (H : Set G)) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr ho.not_two_dvd_nat
  obtain ⟨e,_,_⟩ := hmodel
  have hA : primeRank 2 (MulAut H) ≤ 4 :=
    (_root_.primeRank_le_of_injective 2 (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective).trans alternating_eight_automorphism_two_rank
  have hr := primeRank_le_ker_add (p := 2) (MulAut.conjNormal : G →* MulAut H)
  rw [MulAut.conjNormal_ker_eq_centralizer,hC,zero_add] at hr
  exact hr.trans hA

/-- A.1.31's centralizer restriction and G.10.2 exclude the doubled
natural A₈ row on the original faithful module. -/
theorem not_doubled_natural_eight (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (H : Subgroup G) [H.Normal]
    (hmodel : Section09.Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 8)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)))) : False := by
  have hr := doubled_eight_ambient_two_rank h cover H hmodel
  have hd := h.dimension_bound
  obtain ⟨_,f,_⟩ := hmodel
  have hdim : finrank (ZMod 2) V = 12 := by
    simpa only [Module.finrank_prod,
      BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Fintype.card_fin] using f.finrank_eq
  omega

/-- The proper marked constituent now has only the doubled natural A₆
row. The original centralizer has odd order. The whole marked and
exchanged constituent branches retain their actual source hypotheses. -/
def SixNaturalComponentReduction (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) [IsElementaryAbelian 2 X] : Prop :=
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
      Section10.ComponentOrthogonalData ρ B L ∧
      ∃ I : Submodule (ZMod 2) V, ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
        (v ∈ I ∧ MarkedConstituentAlternative ρ B v X L I hI.isIrrPlus ∧
          (I = ⊤ ∨
            Section09.Quasiequivalent (ρ.comp (componentOrbit L ⊤).subtype)
              ((BinaryPermutation.alternatingNaturalRepresentation (Fin 6)).prod
                (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))) ∧
            finrank (ZMod 2) V = 8 ∧
            Odd (Nat.card (centralizer (componentOrbit L ⊤ : Set G))))) ∨
          (v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I)

/-- Apply the source centralizer obstruction to the original G.11.1(3ii)
hypotheses. This is a reduction; the remaining source alternatives still
require recognition in the original group. -/
theorem conclusion_or_six_natural_component_reduction
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) :
    Conclusion ρ B X ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ SixNaturalComponentReduction ρ B v W X))) := by
  rcases conclusion_or_even_natural_component_reduction h cover hw hS with
    hc | ⟨hi,hd,hs | ⟨hn,hh⟩⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hi,hd,Or.inl hs⟩
  · obtain ⟨L,hL,hm,horth,I,hI,hmarked | hexchanged⟩ := hh
    · obtain ⟨hv,hdata,hwhole | ⟨n,hnat,hmodel,hdim,_⟩⟩ := hmarked
      · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,
          Or.inl ⟨hv,hdata,Or.inl hwhole⟩⟩⟩
      · let := componentOrbit_top_normal L
        rcases hnat with rfl | rfl
        · have hdim8 : finrank (ZMod 2) V = 8 := by simpa using hdim
          exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,
            Or.inl ⟨hv,hdata,Or.inr ⟨hmodel,hdim8,
              natural_centralizer_odd h cover _ 6 hmodel (by simp)⟩⟩⟩⟩
        · exact (not_doubled_natural_eight h cover _ hmodel).elim
    · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,Or.inr hexchanged⟩⟩

end CFSG.Quasithin.ChapterG.Section11
