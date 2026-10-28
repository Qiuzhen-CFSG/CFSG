module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalSylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource

/-!
# The original module misses the exceptional component's two-core

Let C=C_T(K) have order two and let K_D be a C-component of C_G(C)
containing the original A₅ block K. The original pair's two-residual R
centralizes C and normalizes K_D by the source component-orbit theorem.
Thus R normalizes J=K_D C. Irreducibility makes V∩O₂(J) either trivial or V.
In the latter case the original cubic rotation r∈R sends V into O₂(J),
so I=⟨V,Vʳ⟩ lies there. This contradicts r∈I and |r|=3.

The cubic witness gives the same contradiction as the source identity
R=[R,V], without requiring that extra commutator-generation interface.
All containment and normalization refer to the literal subgroupOf maps.
Source: Aschbacher--Smith 13.5.15(7), printed p.920, immediately before
the construction of T₁ and the B₂ argument on p.921.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalCoreIntersection
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceOddRotation SourceOrthogonal SourcePairNormal SourcePairResidualNormal
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

omit [Finite G] in
theorem rotation_mem_residual (v r : G) (hv : v ∈ D.V) (hv2 : v ^ 2 = 1)
    (hr : orderOf r = 3) (hi : v * r * v⁻¹ = r⁻¹) :
    let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
    r ∈ (pResidual 2 I).map I.subtype := by
  dsimp only
  let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
  have hrI : r ∈ I := rotation_mem_pair v r hv hv2 (by decide : Nat.Prime 3)
    (by decide) hr hi
  apply mem_map_of_mem I.subtype (x := ⟨r,hrI⟩)
  apply mem_pResidual_of_orderOf_coprime
  rw [←orderOf_coe (⟨r,hrI⟩ : I),hr]
  decide

/-- Any overgroup normalized by the original pair residual has trivial
intersection of its two-core with the irreducible original module. -/
theorem core_intersection_eq_bot_of_residual_normalizes
    {K : Subgroup G} (hK : K ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : (K.subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (v r : G) (hv : v ∈ D.V) (hv2 : v ^ 2 = 1)
    (hr : orderOf r = 3) (hinv : v * r * v⁻¹ = r⁻¹)
    (J : Subgroup G) (hKJ : K ≤ J)
    (hRJ : let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
      (pResidual 2 I).map I.subtype ≤ normalizer (J : Set G)) :
    D.V ⊓ J.pCoreIn 2 = ⊥ := by
  let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
  let R := (pResidual 2 I).map I.subtype
  have hcoreNorm : normalizer (J : Set G) ≤ normalizer (J.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image J (pCore 2 J)
  have hKW : K ≤ normalizer (D.V ⊓ J.pCoreIn 2 : Set G) :=
    (le_inf (hK.trans (le_sup_left.trans d.normalizes_V))
      (hKJ.trans (J.le_normalizer.trans hcoreNorm))).trans
        inf_normalizer_le_normalizer_inf
  rcases SourceFiveSpan.invariant_subgroup d hK a hi _ inf_le_left hKW with hz | he
  · exact hz
  · have hVP : D.V ≤ J.pCoreIn 2 := he.symm.le.trans inf_le_right
    have hrR : r ∈ R := rotation_mem_residual v r hv hv2 hr hinv
    have hrI : r ∈ I := (map_subtype_le _) hrR
    have heq := mem_normalizer_iff_map_conj_eq.mp (hcoreNorm (hRJ hrR))
    have hIP : I ≤ J.pCoreIn 2 := sup_le hVP ((map_mono hVP).trans_eq heq)
    have hc := (isPGroup_pCoreIn 2 J).orderOf_coprime
      (by decide : Nat.Coprime 2 3) ⟨r,hIP hrI⟩
    rw [←orderOf_coe (⟨r,hIP hrI⟩ : J.pCoreIn 2),hr] at hc
    exact ((by decide : ¬ Nat.Coprime 3 3) hc).elim

include d in
/-- The genuine order-two centralizer has the SQTK two-core quotient needed
by the source component-orbit and containment theorems. -/
theorem exceptional_centralizer_sqtk_quotient (g : D.L)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    IsSQTK KnownSimple.IsKnownSimple
      (centralizer (C : Set G) ⧸ pCore 2 (centralizer (C : Set G))) := by
  let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
  let GD := centralizer (C : Set G)
  have hCne : C ≠ ⊥ := by
    intro he
    change Nat.card C = 2 at hcard
    rw [he,card_bot] at hcard
    contradiction
  let : IsCyclic C := isCyclic_of_prime_card (p := 2) hcard
  have hcore : C ≤ GD.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (D.T.isPGroup'.to_le inf_le_left)
      C.le_centralizer (centralizer_le_normalizer (C : Set G))
  apply Chapter1.Section02.uniqueness_local_quotient_sqtk d.counterexample.qtke
  change GD.pCoreIn 2 ≠ ⊥
  intro he
  exact hCne (bot_unique (hcore.trans he.le))

include d in
/-- The actual residual centralizes C and normalizes every ambient component
of C_G(C), with its two-perfect hypothesis and quotient input discharged. -/
theorem residual_normalizes_component
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (I : Subgroup G) (hIH : I ≤ D.H) (hcore : I.pCoreIn 2 = D.UH)
    (hI : D.H ≤ normalizer (I : Set G)) (KD : Subgroup G)
    (hKDGD : KD ≤ centralizer
      (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))
    (hcomp : (KD.subgroupOf (centralizer
      (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))).IsCComponent)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    let R := (pResidual 2 I).map I.subtype
    R ≤ centralizer (C : Set G) ∧ R ≤ normalizer (KD : Set G) := by
  let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
  let GD := centralizer (C : Set G)
  let R := (pResidual 2 I).map I.subtype
  have hsub : C ≤ (D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) :=
    inf_le_inf_left _ (centralizer_le hL)
  have hRGD : R ≤ GD :=
    (SourcePairCentralizer.residual_centralizes_local_sylow_centralizer
      d h e hseed hn hU I hIH hcore hI).trans (centralizer_le hsub)
  let eR := (subgroupOfEquivOfLe hRGD).symm
  have hpR : IsPPerfect 2 (R.subgroupOf GD) :=
    (isPPerfect_embedded_pResidual 2 I).of_surjective eR.toMonoidHom eR.surjective
  have hQ := exceptional_centralizer_sqtk_quotient d g hcard
  have hN := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ hcomp hpR
  have hm := (map_mono (f := GD.subtype) hN).trans
    ((KD.subgroupOf GD).le_normalizer_map GD.subtype)
  rw [map_subgroupOf_eq_of_le hRGD,map_subgroupOf_eq_of_le hKDGD] at hm
  exact ⟨hRGD,hm⟩

include d in
/-- The original source hypotheses supply a cubic pair and its normalization
of K_D, and hence the precise trivial core intersection used on p.920. -/
theorem exists_original_core_disjoint
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (KD : Subgroup G) (hKDK : NormalBranch.K D g.val ≤ KD)
    (hKDGD : KD ≤ centralizer
      (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))
    (hcomp : (KD.subgroupOf (centralizer
      (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))).IsCComponent)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    ∃ r ∈ D.H, orderOf r = 3 ∧
      let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
      let R := (pResidual 2 I).map I.subtype
      let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
      r ∈ R ∧ I.pCoreIn 2 = D.UH ∧ D.H ≤ normalizer (I : Set G) ∧
      R ≤ centralizer (C : Set G) ∧ R ≤ normalizer (KD : Set G) ∧
      D.V ⊓ (KD ⊔ C).pCoreIn 2 = ⊥ := by
  obtain ⟨v,hv,hvq,hv2,p,hp,hp2,r,hrH,hr,hinv⟩ := exists_odd_rotation h hU
  obtain ⟨hp3,_⟩ := odd_rotation_is_cubic d h e hseed hn hU v r hv hv2 hp hp2 hr hrH hinv
  have hr3 : orderOf r = 3 := hr.trans hp3
  let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
  let R := (pResidual 2 I).map I.subtype
  let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
  have hcore := SourcePairExact.core_eq_closure d h e hseed hn hU
    v r hv hvq hv2 hr3 hrH hinv
  have hI := whole_normalizes_pair d h e hseed hn hU v r hv hv2 hr3 hrH hinv
  obtain ⟨hRC,hRKD⟩ := residual_normalizes_component d h e hseed hn hU g hL
    I (pair_le h hrH) hcore hI KD hKDGD hcomp hcard
  have hRJ : R ≤ normalizer ((KD ⊔ C : Subgroup G) : Set G) :=
    (le_inf hRKD (hRC.trans (centralizer_le_normalizer (C : Set G)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup KD C)
  exact ⟨r,hrH,hr3,rotation_mem_residual v r hv hv2 hr3 hinv,hcore,hI,hRC,hRKD,
    core_intersection_eq_bot_of_residual_normalizes d hK a hi v r hv hv2 hr3 hinv
      (KD ⊔ C) (hKDK.trans le_sup_left) hRJ⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalCoreIntersection
end
