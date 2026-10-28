module
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.OuterMaximum
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.CenterPlacement
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.CenterCount
public import Theory.GroupTheory.SylowInnerAction
public import Theory.GroupTheory.PrimeRankAutomorphismOrder
/-! # Outer elementary actors on an actual symplectic Sylow subgroup
A two-group of automorphisms containing the inner Sylow has its inner
actors represented in that Sylow. In even field degree, field descent
bounds a noninner involution's fixed group. In odd degree, every fixed
involution lies in the Sylow center and the actual fixed-center count
bounds the inner kernel. The cyclic outer quotient adds at most one rank.
Thus the rank is at most 2n+1, strictly below the 3n root-wing rank for n>1.
Source: Aschbacher--Smith 2.5.7, printed p.555, using the symplectic Sylow
geometry and outer involution types. No graph cocycle descent is needed.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.SylowOuterRank
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {F:Type*} [Field F] [Finite F] [CharP F 2]
theorem elementary_outer_rank_le {n : ℕ}
    (hF : Nat.card F=2^n) (hn:1<n)
    (P:Sylow 2 (Sp F)) (R:Subgroup (MulAut (Sp F)))
    (hR:IsPGroup 2 R)
    (hPR:(P:Subgroup (Sp F)).map (MulAut.conj : Sp F→*MulAut (Sp F))≤R)
    (hRP:∀ a∈R, (P:Subgroup (Sp F)).map a.toMonoidHom=P)
    (E : Subgroup (MulAut (Sp F))) (hE : IsElementaryAbelian 2 E)
    (hER:E≤R) (hi : ¬ E ≤ MulAut.innerSubgroup (Sp F)) :
    primeRank 2 E ≤ 2 * n + 1 := by
  have hclass := SemilinearClassification.inner_field_of_preservesDiagram (F:=F)
  let := ExceptionalGraph.outer_isCyclic_of_card hF hn hclass
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  let ie : Sp F ≃* MulAut.innerSubgroup (Sp F) :=
    MonoidHom.ofInjective inner_injective
  have hout : primeRank 2 (MulAut.Outer (Sp F)) ≤ 1 := by
    let P := Classical.choice (inferInstance : Nonempty (Sylow 2 (MulAut.Outer (Sp F))))
    exact P.primeRank_le_one_of_isCyclic inferInstance
  obtain ⟨a, haE, ha⟩ := SetLike.not_le_iff_exists.mp hi
  have hao : orderOf a = 2 := by
    have hs : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) a haE
    have hne : a ≠ 1 := fun h => ha (h ▸ (MulAut.innerSubgroup (Sp F)).one_mem)
    exact orderOf_eq_prime_iff.mpr ⟨hs, hne⟩
  let π : E →* MulAut.Outer (Sp F) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp E.subtype
  let j : π.ker →* MulAut.innerSubgroup (Sp F) := {
    toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let k : π.ker →* Sp F := ie.symm.toMonoidHom.comp j
  have hk (x : π.ker) : MulAut.conj (k x) = x.val.val := by
    exact congrArg Subtype.val (ie.apply_symm_apply (j x))
  let f : π.ker →* a.fixedSubgroup := k.codRestrict _ (fun x => by
    rw [MulAut.mem_fixedSubgroup]
    apply inner_injective
    have he : a * MulAut.conj (k x) * a⁻¹ = MulAut.conj (a (k x)) := by
      ext y
      simp
    rw [← he, hk]
    have hc := congrArg Subtype.val (mul_comm (⟨a, haE⟩ : E) x.val)
    change a * x.val.val = x.val.val * a at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one])
  have hf : Function.Injective f := by
    intro x y h
    have hxy := congrArg (fun z : a.fixedSubgroup => MulAut.conj z.val) h
    change MulAut.conj (k x) = MulAut.conj (k y) at hxy
    rw [hk, hk] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hker : primeRank 2 π.ker ≤ 2*n := by
    obtain hi' | ⟨g,hg,hc⟩ := involution_inner_or_twist hF hn hclass a hao
    · obtain ⟨g,_,rfl⟩ := hi'
      exact False.elim (ha ⟨g,rfl⟩)
    · rcases Nat.even_or_odd n with he | ho
      · have hc' : g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n/2)) g=1 := by
          simpa only [graph_pow_eq_field_of_even he] using hc
        have hconj : IsConj a (fieldAutomorphism (frobeniusEquiv F 2 ^ (n/2))) := by
          rw [hg,graph_pow_eq_field_of_even he]
          exact (half_frobenius_twist_isConj hF hn he g hc').symm
        have hr := EvenTwoRank.outer_fixed_rank_le_of_models hF hn ?_ a (Or.inl ⟨he,hconj⟩)
        · exact (primeRank_le_of_injective 2 f hf).trans hr
        · intro m hm
          subst n
          exact ⟨EvenTwoRank.OuterMaximum.suzukiFixedEquiv m hF⟩
      · have hmove : ¬PreservesDiagram a := by
          have hq : 2<Nat.card F := by
            rw [hF]
            exact (show 2^1<2^n from Nat.pow_lt_pow_right (by decide) hn)
          let ρ:=parabolicClassAction hq
          have hs : ρ (ExceptionalGraph.graphAut (F:=F))^2=1 := by
            rw [←map_pow,ExceptionalGraph.graphAut_square]
            exact (mem_parabolicClassAction_ker_iff hq _).mpr (field_preservesDiagram _)
          have hpow : ρ (ExceptionalGraph.graphAut (F:=F))^n=ρ ExceptionalGraph.graphAut := by
            obtain ⟨m,hm⟩:=ho
            rw [hm,pow_add,pow_mul,hs,one_pow,pow_one,one_mul]
          intro hpres
          have heq : ρ a=1 := (mem_parabolicClassAction_ker_iff hq _).mpr hpres
          rw [hg,map_mul,map_pow,hpow,
            show ρ (MulAut.conj g)=1 from
              (mem_parabolicClassAction_ker_iff hq _).mpr (inner_preservesDiagram g),one_mul] at heq
          exact ExceptionalGraph.graphAut_not_preservesDiagram
            ((mem_parabolicClassAction_ker_iff hq _).mp heq)
        have haP:=hRP a (hER haE)
        let f' : π.ker→*SwappingFixedRank.fixedCenter P a := k.codRestrict _ (fun x=>by
          refine ⟨?_,(f x).property⟩
          apply SwappingFixedRank.central_placement hF hn P a haP hmove
          · apply MulAut.inner_mem_image_sylow EvenProjective.center_eq_bot P R hR hPR
            rw [hk]
            exact hER x.val.property
          · apply inner_injective
            rw [map_pow,hk,map_one]
            exact elemPow_eq_one_of_isElementaryAbelian (A:=E) _ x.val.property
          · have ht := (f x).property
            rw [MulAut.mem_fixedSubgroup] at ht
            exact ht)
        have hf' : Function.Injective f' := by
          intro x y h
          apply hf
          apply Subtype.ext
          change k x=k y
          exact congrArg (fun z:SwappingFixedRank.fixedCenter P a=>(z:Sp F)) h
        have hcard : Nat.card π.ker ≤ 2^n :=
          (Nat.card_le_card_of_injective f' hf').trans
            (hF ▸ (SwappingFixedRank.fixedCenter_card_bounds hF hn P a haP hmove).1)
        have hb := Theory.GroupTheory.primeRank_le_of_card_le_prime_pow
          (G:=π.ker) (p:=2) hcard
        omega
  have hb := primeRank_le_ker_add (p := 2) π
  omega

end Theory.SpecificGroups.SymplecticFour.SylowOuterRank
