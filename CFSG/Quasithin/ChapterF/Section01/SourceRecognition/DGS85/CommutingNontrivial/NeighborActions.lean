module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear.MatrixBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.SpecificGroups.SU3.IsotropicBorelAction
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.GroupAction.MatchedPointOrbit

/-!
# Marked local neighbor actions for the radius-three argument

The actual graph edge stabilizer inside L is the normalizer of its marked
Sylow. Matrix Borels identify these normalizers with point stabilizers in
the linear, Suzuki and unitary actions. Matching their inverse images
therefore transports two-transitivity to the original graph neighbors.
For SU₃, the central scalar projection recovers exactly the Sylow normalizer;
no Sylow is identified with its full projective preimage. All binary field
parameters and arbitrary Hermitian forms are included. D₁₀ is retained as
an explicit exceptional isomorphism, not assigned a doubly transitive action.

`RadiusThreeCore` consumes these actions in the original 6.5 obstruction.
Source: DGS, *Groups and Graphs* (1985), 8.4(1), printed p.137;
Huppert II.10.12 for the marked unitary action.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
private theorem two_pretransitive_comp {A D X : Type*} [Group A] [Group D]
    [MulAction D X] (f : A →* D) (hf : Function.Surjective f)
    (ht : MulAction.IsMultiplyPretransitive D X 2) :
    @MulAction.IsMultiplyPretransitive A X _ (MulAction.compHom X f) 2 := by
  let : MulAction A X := MulAction.compHom X f
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g,hg,hg'⟩ := MulAction.is_two_pretransitive_iff.mp ht hab hcd
  obtain ⟨x,rfl⟩ := hf g
  exact ⟨x,hg,hg'⟩

private theorem projective_sylow_point {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 0 < n)
    (hc : Nat.card K = (2^n)^2) (hf : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    let X := BenderSuzuki.Converse.psuOmega (Unitary.FormTransport.standardForm J)
    ∃ (a : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) X) (o : X),
      @MulAction.stabilizer _ _ _ a o = normalizer (T : Set _) ∧
      @MulAction.IsMultiplyPretransitive _ X _ a 2 := by
  dsimp only
  let J₀ := Unitary.FormTransport.standardForm J
  obtain ⟨C,hC,g,hT⟩ := Unitary.psu_sylow_normalizer_eq_matrix_borel J n hn hc hf T
  obtain ⟨_,a,o,ho,ht⟩ := HermitianForm.IsotropicBorelAction.exists_action J₀ rfl (2^n)
    hc (Unitary.fixed_card J n hn hc hf)
  let := a
  let e := Unitary.FormTransport.projectiveEquiv J C hC
  let a' : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (BenderSuzuki.Converse.psuOmega J₀) :=
    MulAction.compHom _ e.toMonoidHom
  refine ⟨a',g • o,?_,two_pretransitive_comp e.toMonoidHom e.surjective ht⟩
  change (MulAction.stabilizer _ (g • o)).comap e.toMonoidHom = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,ho]
  exact hT.symm

private theorem special_sylow_point {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 0 < n)
    (hc : Nat.card K = (2^n)^2) (hf : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 J.specialSubgroup) :
    let X := BenderSuzuki.Converse.psuOmega (Unitary.FormTransport.standardForm J)
    ∃ (a : MulAction J.specialSubgroup X) (o : X),
      @MulAction.stabilizer _ _ _ a o = normalizer (T : Set _) ∧
      @MulAction.IsMultiplyPretransitive _ X _ a 2 := by
  dsimp only
  obtain ⟨a,o,ho,ht⟩ := projective_sylow_point J hn hc hf
    (T.mapSurjective J.specialToProjective_surjective)
  let := a
  let a' : MulAction J.specialSubgroup (BenderSuzuki.Converse.psuOmega
      (Unitary.FormTransport.standardForm J)) := MulAction.compHom _ J.specialToProjective
  refine ⟨a',o,?_,two_pretransitive_comp _ J.specialToProjective_surjective ht⟩
  change (MulAction.stabilizer _ o).comap J.specialToProjective = _
  rw [ho]
  exact T.normalizer_comap_of_central_kernel _ J.specialToProjective_surjective
    J.specialToProjective_ker_le_center

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem source_edge_transitive_of_action (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {D X : Type*} [Group D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D)
    (hp : ∀ T : Sylow 2 D, ∃ (a : MulAction D X) (o : X),
      @MulAction.stabilizer _ _ _ a o = normalizer (T : Set D) ∧
      @MulAction.IsMultiplyPretransitive D X _ a 2)
    {x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y) (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  let T := R.mapSurjective hq
  obtain ⟨a,o,ho,ht⟩ := hp T
  let := a
  have hk : q.ker = pCore 2 L := by
    ext t
    change e (QuotientGroup.mk' (pCore 2 L) t) = 1 ↔ t ∈ pCore 2 L
    rw [map_eq_one_iff _ e.injective]
    exact QuotientGroup.eq_one_iff t
  have hpre : (T : Subgroup D).comap q = R :=
    comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal R)
  have hstab : (MulAction.stabilizer D o).comap q = MulAction.stabilizer L w := by
    rw [ho]
    change (normalizer ((T : Subgroup D) : Set D)).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,hpre,Sylow.coe_coe,
      ← (source_edge_local_normalizer h d hvw M R hR).2]
    rfl
  have hn : (normalizer (R : Set L)).map q = normalizer (T : Set D) :=
    R.normalizer_map_surjective q hq
  obtain ⟨l,hl,hlx⟩ := d.transitive v ⟨w,hvw⟩ ⟨x,hx⟩
  obtain ⟨r,hr,hry⟩ := d.transitive v ⟨w,hvw⟩ ⟨y,hy⟩
  obtain ⟨t,htN,he⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base q
    (normalizer (R : Set L)) w o hstab (by
      intro a b ha hb
      obtain ⟨t,hto,htab⟩ := MulAction.is_two_pretransitive_iff.mp ht ha.symm hb.symm
      exact ⟨t,by rw [hn,←ho]; exact hto,htab⟩)
    (⟨l,hl⟩ : L) (⟨r,hr⟩ : L)
    (by change l • w ≠ w; rwa [hlx]) (by change r • w ≠ w; rwa [hry])
  refine ⟨t,⟨t.property,?_⟩,?_⟩
  · rwa [← (source_edge_local_normalizer h d hvw M R hR).2] at htN
  · change (t : G) • (l • w) = r • w at he
    rwa [hlx,hry] at he

/-- The unitary quotient's marked Borel makes the actual local edge actor
transitive on the other graph neighbors. Special and projective models,
arbitrary Hermitian forms and the binary field are all retained. -/
theorem source_unitary_edge_transitive (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {n : ℕ} (hn : 0 < n)
    (hu : ClassicalGroup.IsPSU (d.localGroup v ⧸ pCore 2 (d.localGroup v)) 3 (2^n) ∨
      IsSU (d.localGroup v ⧸ pCore 2 (d.localGroup v)) 3 (2^n))
    {x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y) (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y := by
  rcases hu with hu | hu
  · have M := IsRankOneModel.projective_unitary n hn hu
    obtain ⟨K,_,_,J,hc,hf,⟨e⟩⟩ := hu
    exact source_edge_transitive_of_action h hB d hvw M e
      (projective_sylow_point J hn hc hf) hx hy hxw hyw
  · have M := IsRankOneModel.special_unitary n hn hu
    obtain ⟨K,_,_,J,hc,hf,⟨e⟩⟩ := hu
    exact source_edge_transitive_of_action h hB d hvw M e
      (special_sylow_point J hn hc hf) hx hy hxw hyw


open scoped MatrixGroups
open BenderSuzuki.Converse

private theorem linear_sylow_point {K : Type*} [Field K] [Finite K] [CharP K 2]
    (T : Sylow 2 (SL2 K)) :
    ∃ (a : MulAction (SL2 K) (P1 K)) (o : P1 K),
      @MulAction.stabilizer _ _ _ a o = normalizer (T : Set _) ∧
      @MulAction.IsMultiplyPretransitive _ (P1 K) _ a 2 := by
  let S := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL2 K) S T
  have hmap : (S : Subgroup (SL2 K)).map (MulAut.conj g).toMonoidHom = T :=
    congrArg Sylow.toSubgroup hg
  have hs : (S : Subgroup (SL2 K)) = Unip K := Linear.unip_eq_upper.symm
  refine ⟨inferInstance,g • pInf K,?_,inferInstance⟩
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  change (Borel K).map (MulAut.conj g).toMonoidHom = _
  rw [← Linear.unip_normalizer,← hs,map_equiv_normalizer_eq,hmap]
  rfl

private theorem suzuki_borel_point (m : ℕ) :
    SuzukiBorelSubgroup m = MulAction.stabilizer (SuzukiMatrixGroup m) (suzukiOvoidInfinity m) := by
  have hroot (g : SuzukiMatrixGroup m) (hg : g ∈ SuzukiRootSubgroup m) :
      g • suzukiOvoidInfinity m = suzukiOvoidInfinity m := by
    obtain ⟨a,b,hab⟩ := (mem_suzukiRootSubgroup_iff m g).mp hg
    apply Subtype.ext
    rw [suzukiOvoid_smul_val]
    change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv •
      Projectivization.mk _ ![1,0,0,0] _ = Projectivization.mk _ ![1,0,0,0] _
    rw [hab,Projectivization.smul_mk,Projectivization.mk_eq_mk_iff']
    refine ⟨1,?_⟩
    funext i
    fin_cases i <;> simp [SuzukiRootGL,SuzukiRootMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
  have hRB : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_left
  apply le_antisymm
  · rw [suzukiBorelSubgroup_eq_sup]
    exact sup_le hroot (fun g hg => (mem_suzukiSplitTorus_iff_fix_pair m g).mp hg |>.1)
  · intro g hg
    have hgi : g • suzukiOvoidInfinity m = suzukiOvoidInfinity m := hg
    have hgz : g • suzukiOvoidZero m ≠ suzukiOvoidInfinity m := by
      intro he
      exact (suzukiOvoidInfinity_ne_zero m).symm ((MulAction.injective g) (he.trans hgi.symm))
    obtain ⟨r,hr,_⟩ := suzukiRootSubgroup_regular m (g • suzukiOvoidZero m)
      (suzukiOvoidZero m) hgz (suzukiOvoidInfinity_ne_zero m).symm
    have ht : (r : SuzukiMatrixGroup m) * g ∈ SuzukiSplitTorus m :=
      (mem_suzukiSplitTorus_iff_fix_pair m _).mpr
        ⟨by rw [mul_smul,hgi,hroot r r.property],by rw [mul_smul,hr]⟩
    have hb : (r : SuzukiMatrixGroup m) * g ∈ SuzukiBorelSubgroup m := by
      rw [suzukiBorelSubgroup_eq_sup]
      exact mem_sup_right ht
    simpa only [inv_mul_cancel_left] using
      (SuzukiBorelSubgroup m).mul_mem ((SuzukiBorelSubgroup m).inv_mem (hRB r.property)) hb

private theorem suzuki_sylow_point (m : ℕ) (T : Sylow 2 (SuzukiMatrixGroup m)) :
    ∃ (a : MulAction (SuzukiMatrixGroup m) (SuzukiOvoid m)) (o : SuzukiOvoid m),
      @MulAction.stabilizer _ _ _ a o = normalizer (T : Set _) ∧
      @MulAction.IsMultiplyPretransitive _ (SuzukiOvoid m) _ a 2 := by
  obtain ⟨g,hg⟩ := suzuki_sylow_normalizer_eq_conjugate_borel m T
  refine ⟨inferInstance,g • suzukiOvoidInfinity m,?_,inferInstance⟩
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,← suzuki_borel_point,hg]

/-- Every source local model other than D₁₀ has the required marked
edge transitivity. The exceptional isomorphism is explicit, including when
the selected catalogue constructor is the degenerate Suzuki model. -/
theorem source_edge_transitive_or_dihedral (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v))) :
    (∀ x y : Vertex (family P), (graph (family P)).Adj v x →
      (graph (family P)).Adj v y → x ≠ w → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y) ∨
      Nonempty ((d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5) := by
  cases M with
  | linear n hn hi =>
    have M := IsRankOneModel.linear n hn hi
    obtain ⟨K,_,_,hc,⟨e⟩⟩ := hi
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact Or.inl (fun _ _ hx hy hxw hyw =>
      source_edge_transitive_of_action h hB d hvw M f linear_sylow_point hx hy hxw hyw)
  | suzuki m hi =>
    have M := IsRankOneModel.suzuki m hi
    obtain ⟨e⟩ := hi
    exact Or.inl (fun _ _ hx hy hxw hyw =>
      source_edge_transitive_of_action h hB d hvw M e (suzuki_sylow_point m) hx hy hxw hyw)
  | projective_unitary n hn hi =>
    exact Or.inl (fun _ _ hx hy hxw hyw =>
      source_unitary_edge_transitive h hB d hvw hn (Or.inl hi) hx hy hxw hyw)
  | special_unitary n hn hi =>
    exact Or.inl (fun _ _ hx hy hxw hyw =>
      source_unitary_edge_transitive h hB d hvw hn (Or.inr hi) hx hy hxw hyw)
  | dihedral hi => exact Or.inr hi


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
