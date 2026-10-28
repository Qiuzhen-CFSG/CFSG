module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank
public import Theory.GroupTheory.PrimeRankCentralizer

/-!
# Nonnormal C-components are ordinary

In the noncentral Fitting case A.3.6 supplies an odd omega subgroup of
rank two and exponent p, with the original conjugation action kernel equal
to the Fitting subgroup. Distinct C-components commute by A.3.7. The ambient
rank bound puts a conjugate omega subgroup inside the original one, hence
makes them equal. This would centralize the entire omega subgroup, contrary
to its action kernel. Thus the Fitting subgroup is central and the original
C-component is quasisimple. The elementary and extraspecial omega cases
share this argument; all positive homocyclic exponents are retained.

Source: Aschbacher–Smith A.3.8(3), printed pp.45–46.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.NonnormalOrdinary
open Chapter1 Chapter1.Section02 Chapter1.Section02.LocalModels Chapter1.RadicalActions

private theorem odd_shape_two_le_rank {Q:Type*} [Group Q] [Finite Q]
    {p:ℕ} [Fact p.Prime] (ho:Odd p) (hQ:XiOddQuotient p Q) : 2≤primeRank p Q := by
  by_contra! hn
  let P:Sylow p Q:=hQ.isPGroup.to_subgroup (⊤:Subgroup Q) |>.toSylow (by
    simp only [index_top];exact (Fact.out:p.Prime).not_dvd_one)
  let : IsCyclic P:=P.isCyclic_of_primeRank_le_one_of_ne_two
    (by intro he; subst p; norm_num at ho) (by omega)
  let e:P≃*Q:=(MulEquiv.subgroupCongr (IsPGroup.toSylow_coe _ _)).trans topEquiv
  exact hQ.not_isCyclic (isCyclic_of_surjective e.toMonoidHom e.surjective)

private theorem odd_shape_pow {Q:Type*} [Group Q] {p:ℕ}
    (hQ:XiOddQuotient p Q) (x:Q) : x^p=1 := by
  rcases hQ with ⟨he,_⟩|⟨_,_,he⟩
  · let :=he
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p Q) x
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (he ▸ dvd_rfl) x

/-- A rank-two subgroup of exponent p centralized by its conjugate is
invariant whenever the ambient p-rank is at most two. -/
private theorem exponent_prime_conjugate_eq {G:Type*} [Group G] [Finite G]
    {p:ℕ} [Fact p.Prime] (hG:primeRank p G≤2)
    (Q:Subgroup G) (hr:2≤primeRank p Q) (hp:∀x:Q,x^p=1)
    (g:G) (hc:Q≤centralizer (Q.map (MulAut.conj g).toMonoidHom:Set G)) :
    Q.map (MulAut.conj g).toMonoidHom=Q := by
  have hrQ:primeRank p Q=2:=le_antisymm
    ((Theory.GroupTheory.primeRank_le_of_injective p Q.subtype Q.subtype_injective).trans hG) hr
  have hle:Q.map (MulAut.conj g).toMonoidHom≤Q := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_of_prime_pow_eq_one_of_centralizes_rank_two hG Q hrQ
    · rw [←map_pow, show x^p=1 from congrArg Subtype.val (hp ⟨x,hx⟩),map_one]
    · intro y hy
      exact (hc hy _ (mem_map_of_mem _ hx)).symm
  apply eq_of_le_of_card_ge hle
  exact (Nat.card_congr ((MulAut.conj g).subgroupMap Q).toEquiv).le

/-- The original pre-ordinary step in A.3.8: a nonnormal C-component of a
two-core-free SQTK group is quasisimple. -/
theorem quasisimple_of_not_normal {G:Type*} [Group G] [Finite G] {κ:GroupClass}
    (hG:IsSQTK κ G) (hO:pCore 2 G=⊥) (B:Subgroup G)
    (hB:B.IsCComponent) (hn:¬B.Normal) : IsQuasisimple B := by
  have hcentral:fittingSubgroup B≤center B := by
    by_contra hf
    obtain ⟨hcon,hw⟩:=NoncentralFitting.conclusion_of_noncentral hG hO hB hf
    have hfit:fittingSubgroup B≠⊥ := by intro he;exact hf (he ▸ bot_le)
    obtain ⟨p,hp,hd⟩:=Nat.exists_prime_and_dvd (show Nat.card (fittingSubgroup B)≠1 from
      fun he=>hfit (eq_bot_iff_card _ |>.mpr he))
    let : Fact p.Prime:=⟨hp⟩
    have hdata:=hw.2.2 p hd
    have ho:Odd p:=hp.odd_of_ne_two (by omega)
    let O:=omegaCore p B
    have hshape:XiOddQuotient p O :=
      (RadicalStructure.core_omega
        (RadicalStructure.nonsimple_radical hcon
          (NoncentralFitting.not_quasisimple_of_noncentral_fitting hf)) hd).2.of_mulEquiv
        ((omega (pCore p B) (p:=p) 1).equivMapOfInjective
          (pCore p B).subtype (pCore p B).subtype_injective)
    let Q:=O.map B.subtype
    let eO:O≃*Q:=O.equivMapOfInjective B.subtype B.subtype_injective
    have hQ:XiOddQuotient p Q:=hshape.of_mulEquiv eO
    obtain ⟨g,hg⟩:∃g:G,B.map (MulAut.conj g).toMonoidHom≠B := by
      by_contra! hh
      exact hn (normal_iff_map_conj_eq.mpr hh)
    have hc:B≤centralizer (B.map (MulAut.conj g).toMonoidHom:Set G):=
      commutator_eq_bot_iff_le_centralizer.mp
        (CComponentCommutation.commutator_eq_bot hG hO hB
          (hB.map_equiv (MulAut.conj g)) hg.symm)
    have hQle:Q≤B:=map_subtype_le _
    have he:=exponent_prime_conjugate_eq (hG.stronglyQuasithin p hp ho) Q
      (odd_shape_two_le_rank ho hQ) (odd_shape_pow hQ) g
      (hQle.trans (hc.trans (centralizer_le (map_mono hQle))))
    have hQC:Q≤centralizer (B:Set G) := by
      rw [←he]
      exact (map_mono hQle).trans (le_centralizer_iff.mp hc)
    have hOC:O≤center B := by
      intro x hx
      exact mem_center_iff.mpr (fun b=>Subtype.ext (hQC (mem_map_of_mem B.subtype hx) b b.property))
    have ht:(⊤:Subgroup B)≤fittingSubgroup B := by
      rw [←hdata.2.1]
      apply le_trans ?_ CenterFrattiniSource.omega_centralizer_le_action_ker
      intro x _ y hy
      exact (mem_center_iff.mp (hOC hy) x).symm
    have htop:fittingSubgroup B=⊤:=top_unique ht
    let : Group.IsSolvable (⊤:Subgroup B):=htop ▸ inferInstanceAs (Group.IsSolvable (fittingSubgroup B))
    exact hB.not_isSolvable (Group.isSolvable_of_surjective
      (f:=(topEquiv:(⊤:Subgroup B)≃*B).toMonoidHom) topEquiv.surjective)
  have hs:solvableRadical B=center B := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hcentral)
    exact le_solvableRadical (center B) inferInstance
      (Group.isSolvable_of_comm (fun a b=>Subtype.ext (mem_center_iff.mp a.property b).symm))
  let :=hB.perfect
  let :=hB.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩

/-- The source normal-or-quasisimple alternative, on actual C-components. -/
theorem normal_or_quasisimple {G:Type*} [Group G] [Finite G] {κ:GroupClass}
    (hG:IsSQTK κ G) (hO:pCore 2 G=⊥) (B:Subgroup G) (hB:B.IsCComponent) :
    B.Normal ∨ IsQuasisimple B := by
  by_cases hn:B.Normal
  · exact Or.inl hn
  · exact Or.inr (quasisimple_of_not_normal hG hO B hB hn)
end CFSG.Quasithin.ChapterA.Section03.NonnormalOrdinary
