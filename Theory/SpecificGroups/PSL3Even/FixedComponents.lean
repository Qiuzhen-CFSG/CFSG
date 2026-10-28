module
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.PSL3Even.FixedComponentRows
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SU3.SixSubgroupExclusion
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import BenderSuzuki.External.Huppert.II.theorem_8_27

/-!
# Fixed components of binary linear-three groups

The full involution rows identify a fixed component with the linear-three
subfield residual, or embed it in a binary linear-two or unitary-three group.
The latter Sylow groups have commuting involutions. In the subfield row,
the two-rank formula forces field degree one when the component has rank
at most two. Thus a component with the source's dihedral or semidihedral
Sylow shape is PSL₃(2), inside PSL₃(4), with its actual field action retained.
The same rows exclude alternating-six components without a rank hypothesis.

Source: Aschbacher–Smith 2.5.19, printed p.561, and 16.1.4(1),(4)–(6),
printed pp.1170–1171; the shared A₆ application is E.6.23, printed p.254.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3Even.FixedComponents
open Matrix.PSL3Even.InvolutionResidualRows
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm

private theorem perfect_le_twoResidual {H:Type*} [Group H] [Finite H]
    (D:Subgroup H) [Group.IsPerfect D] : D≤pResidual 2 H := by
  let : Group.IsNilpotent (H⧸pResidual 2 H) :=
    (Subgroup.isPGroup_quotient_pResidual (G:=H) 2).isNilpotent
  exact (le_solvableResidual_of_isPerfect D).trans
    (solvableResidual_le_of_solvable_quotient (pResidual 2 H))

private noncomputable def perfectResidualEmbedding {H R:Type*} [Group H] [Finite H]
    [Group R] (D:Subgroup H) [Group.IsPerfect D] (e:pResidual 2 H≃*R) : D→*R :=
  e.toMonoidHom.comp (inclusion (perfect_le_twoResidual D))

private theorem perfectResidualEmbedding_injective {H R:Type*} [Group H] [Finite H]
    [Group R] (D:Subgroup H) [Group.IsPerfect D] (e:pResidual 2 H≃*R) :
    Function.Injective (perfectResidualEmbedding D e) :=
  e.injective.comp (inclusion_injective _)

private theorem component_equiv_residual {H:Type*} [Group H] [Finite H]
    [IsSimpleGroup (pResidual 2 H)] (D:Subgroup H) (hD:IsComponent H D) :
    Nonempty (D≃*pResidual 2 H) := by
  let :=hD.2
  have hle:=perfect_le_twoResidual D
  let e:=subgroupOfEquivOfLe hle
  let : IsSimpleGroup (D⧸center D):=IsQuasisimple.simple
  let : Nontrivial D:=(QuotientGroup.mk'_surjective (center D)).nontrivial
  let : Nontrivial (D.subgroupOf (pResidual 2 H)):=e.nontrivial
  have ht:D.subgroupOf (pResidual 2 H)=⊤ := by
    rcases hD.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup (pResidual 2 H)) with hb|ht
    · exact ((nontrivial_iff_ne_bot _).mp inferInstance hb).elim
    · exact ht
  exact ⟨e.symm.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)⟩

private theorem sylow_involutions_commute_of_injective {D H:Type*}
    [Group D] [Finite D] [Group H] [Finite H]
    (P:Sylow 2 D) (Q:Sylow 2 H)
    (hQ:∀x y:Q,x^2=1→y^2=1→Commute x y)
    (f:D→*H) (hf:Function.Injective f) :
    ∀x y:P,x^2=1→y^2=1→Commute x y := by
  obtain ⟨Q',hQ'⟩ := (P.isPGroup'.map f).exists_le_sylow
  let e:Q'≃*Q:=Q'.equiv Q
  let r:P→*Q:=e.toMonoidHom.comp ((f.comp (P:Subgroup D).subtype).codRestrict Q'
    (fun x=>hQ' ⟨x,x.property,rfl⟩))
  have hr:Function.Injective r := by
    intro x y h
    apply Subtype.ext
    exact hf (congrArg Subtype.val (e.injective h))
  intro x y hx hy
  apply hr
  exact (show r (x*y)=r (y*x) from by
    simpa only [map_mul] using (hQ (r x) (r y)
      (by rw [←map_pow,hx,map_one]) (by rw [←map_pow,hy,map_one])).eq)

private theorem binary_two_sylow_commute {F:Type*} [Field F] [Finite F]
    {n:ℕ} (hF:Nat.card F=2^n) (Q:Sylow 2 PSL(2,F)) :
    ∀x y:Q,x^2=1→y^2=1→Commute x y := by
  obtain ⟨e⟩:=BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  intro x y _ _
  exact e.symm.injective (by simp only [map_mul];exact mul_comm _ _)

private theorem binary_unitary_sylow_commute {F:Type*} [Field F] [Finite F]
    (J:HermitianForm 3 F) {m:ℕ} (hm:0<m) (hF:Nat.card F=(2^m)^2)
    (hf:Nat.card {x:F // J.conj x=x}=2^m)
    {D:Type*} [Group D] [Finite D] (P:Sylow 2 D)
    (f:D→*ProjectiveSpecialUnitaryMatrixGroup J) (hi:Function.Injective f) :
    ∀x y:P,x^2=1→y^2=1→Commute x y := by
  open OddPrimeSylow.NormalizedOuter.FormTransport in
  obtain ⟨e⟩:=exists_projectiveEquiv J (2^m) hF hf
  let K:=OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let : Finite (ProjGenLinGroup (Fin 3) F):=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup K):=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact sylow_involutions_commute_of_injective P
    (EvenTwoRank.rootSylow K rfl hm hF hf)
    (EvenTwoRank.rootSylow_involutions_commute K rfl hm hF hf)
    (e.toMonoidHom.comp f) (e.injective.comp hi)

/-- A fixed component with rank at most two and noncommuting Sylow
involutions in binary PSL₃ is the binary subfield component in PSL₃(4). -/
theorem component_field_degree_two {F:Type*} [Field F] [Finite F]
    {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (a:MulAut PSL(3,F)) (ha:orderOf a=2)
    (D:Subgroup a.fixedSubgroup) (hD:IsComponent a.fixedSubgroup D)
    (hr:primeRank 2 D≤2) (P:Sylow 2 D)
    (hnc:¬∀x y:P,x^2=1→y^2=1→Commute x y) :
    n=2 ∧ FieldCase n a ∧ Nonempty (D≃*Matrix.PSL3Two.PSL) := by
  let : IsQuasisimple D:=hD.2
  rcases fixed_component_rows hn hF a ha with hs|hf|hg|hu
  · let :=hs
    exact (hD.isCComponent.not_isSolvable inferInstance).elim
  · obtain ⟨g,σ,hσ,he,hσ2,hconj,m,hm,hnm,hK,⟨er⟩⟩:=hf
    let K:=FixedBy.subfield F σ
    let : Group.IsPerfect PSL(3,K):=Atlas.psl_perfect 3 (by decide)
    let eR:pResidual 2 a.fixedSubgroup≃*PSL(3,K):=
      er.trans ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv)
    let : IsSimpleGroup PSL(3,K):=Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup (pResidual 2 a.fixedSubgroup):=eR.isSimpleGroup
    obtain ⟨ed⟩:=component_equiv_residual D hD
    let eD:=ed.trans eR
    have hrK:primeRank 2 PSL(3,K)≤2 := by rw [←primeRank_equiv 2 eD];exact hr
    rw [Matrix.PSL3Even.two_rank K hm hK] at hrK
    have hm1:m=1:=by omega
    have hn2:n=2:=by omega
    let : Fintype K:=Fintype.ofFinite K
    let eF:K≃+*ZMod 2:=FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card]
      simpa only [hm1,pow_one,ZMod.card] using hK)
    exact ⟨hn2,⟨g,σ,hσ,he,hσ2,hconj,m,hm,hnm,hK,⟨er⟩⟩,⟨eD.trans (Atlas.fieldEquivPSL 3 eF)⟩⟩
  · obtain ⟨_,_,_,⟨er⟩⟩:=hg
    let f:D→*PSL(2,F):=(commutator PSL(2,F)).subtype.comp (perfectResidualEmbedding D er)
    have hi:Function.Injective f:=Subtype.val_injective.comp (perfectResidualEmbedding_injective D er)
    exact (hnc (sylow_involutions_commute_of_injective P (default:Sylow 2 PSL(2,F))
      (binary_two_sylow_commute hF _) f hi)).elim
  · obtain ⟨m,J,hm,_,_,hc,hfix,⟨er⟩⟩:=hu
    exact (hnc (binary_unitary_sylow_commute J (by omega) hc hfix P
      (perfectResidualEmbedding D er) (perfectResidualEmbedding_injective D er))).elim
private theorem card_psl_three_ne_six {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) : Nat.card PSL(3,F) ≠ 360 := by
  intro hc
  have he := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [hc] at he
  by_cases hn1 : n = 1
  · subst n
    norm_num [hF] at he
  · have hq : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 2 ≤ n by omega)
    have hg : Nat.gcd 3 (Nat.card F - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hbig : 60480 ≤ Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
      calc
        60480 = 4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1) := by norm_num
        _ ≤ _ := by gcongr
    omega

/-- No involution in a binary linear-three group has an alternating-six
component in its actual fixed subgroup. -/
theorem not_alternating_six_component {F:Type*} [Field F] [Finite F]
    {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (a:MulAut PSL(3,F)) (ha:orderOf a=2)
    (D:Subgroup a.fixedSubgroup) (hD:IsComponent a.fixedSubgroup D) :
    ¬ Nonempty (D≃*alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  let : IsQuasisimple D:=hD.2
  rcases fixed_component_rows hn hF a ha with hs|hf|hg|hu
  · let :=hs
    exact hD.isCComponent.not_isSolvable inferInstance
  · obtain ⟨_,σ,_,_,_,_,m,hm,_,hK,⟨er⟩⟩:=hf
    let K:=FixedBy.subfield F σ
    let : Group.IsPerfect PSL(3,K):=Atlas.psl_perfect 3 (by decide)
    let eR:pResidual 2 a.fixedSubgroup≃*PSL(3,K):=
      er.trans ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv)
    let : IsSimpleGroup PSL(3,K):=Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup (pResidual 2 a.fixedSubgroup):=eR.isSimpleGroup
    obtain ⟨ed⟩:=component_equiv_residual D hD
    exact card_psl_three_ne_six hm hK
      ((Nat.card_congr (((ed.trans eR).symm.trans e).toEquiv)).trans
        alternatingGroup.SixSubgroupObstructions.card_six)
  · obtain ⟨_,_,_,⟨er⟩⟩:=hg
    let f:D→*PSL(2,F):=(commutator PSL(2,F)).subtype.comp (perfectResidualEmbedding D er)
    have hi:Function.Injective f:=Subtype.val_injective.comp (perfectResidualEmbedding_injective D er)
    exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute
      (default:Sylow 2 PSL(2,F)) (binary_two_sylow_commute hF _)
      (f.comp e.symm.toMonoidHom) (hi.comp e.symm.injective)
  · obtain ⟨m,J,hm,_,_,hc,hfix,⟨er⟩⟩:=hu
    exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute
      (default:Sylow 2 D) (binary_unitary_sylow_commute J (by omega) hc hfix _
        (perfectResidualEmbedding D er) (perfectResidualEmbedding_injective D er))
      e.symm.toMonoidHom e.symm.injective
end Matrix.PSL3Even.FixedComponents
