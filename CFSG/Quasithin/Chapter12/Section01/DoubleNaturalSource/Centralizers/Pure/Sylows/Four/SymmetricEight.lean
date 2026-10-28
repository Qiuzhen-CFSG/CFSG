module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Radical
public import Theory.GroupTheory.WeakClosureSylowTransport

/-!
# The marked S₈ parabolic contradiction

The Klein product on two four-point blocks is the unique elementary sixteen
in the even part of the binary-tree Sylow. This proves its weak closure in
S₈, and Sylow conjugacy transports that statement to every containing
two-group. Its full normalizer is the unordered four-block stabilizer.

The literal two-residual of that stabilizer contains the Klein product:
irreducibility of the core reduces this to one nontrivial commutator with
an odd-order permutation. Thus its two-core is precisely the Klein product.
These model facts discharge both radical properties in Radical.lean whenever
an actual quotient isomorphism carries the original residual to this model.
The final chosen-module application excludes every such marking of the
constructed faithful component quotient. No abstract family tag or order-only
recognition is used, and the corrected Held alternative remains present.

Constructing the source marking, maximality and the remaining component
exclusions, including L₅(2), stays with qt-d-double-natural-pure-fusion.
The exact fixed-subgroup premise stays explicit for that owner and the
existing qt-rank-two-ms93 source producer. The final earlier-input assembly
owner is qt-d-double-natural-centralizers; this is not completed 12.1.4.
Source: Aschbacher--Smith 12.1.4, pp.790--791, I.2.5, p.414, and the
existing attributed H.9.3 eight-point catalogue, pp.391--392.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi.SymmetricEight
open BinaryNaturalDual.FourActors BinaryNaturalDual.FourActors.PermutationCatalogue
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

private theorem radical_even : permutationA0 ≤ alternatingGroup (Fin 8) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    apply Equiv.Perm.mem_alternatingGroup.mpr <;> decide +kernel

private theorem radical_weakly_closed_tree (g : S)
    (hg : permutationA0.map (MulAut.conj g).toMonoidHom ≤ treeGroup) :
    permutationA0.map (MulAut.conj g).toMonoidHom = permutationA0 := by
  let : IsElementaryAbelian 2 permutationA0 := permutationActor_elementary 0
  let := IsElementaryAbelian.map (p := 2) (A := permutationA0) (MulAut.conj g).toMonoidHom
  apply permutation_even_tree_eq_A0_of_card_ge
  · refine le_inf hg ?_
    rintro _ ⟨x,hx,rfl⟩
    exact (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem x (radical_even hx) g
  · rw [card_map_of_injective (MulAut.conj g).injective]
    exact (permutationActor_card 0).ge

/-- The actual parabolic radical is weakly closed in every containing two-group. -/
theorem radical_weakly_closed (U : Subgroup S) (hU : IsPGroup 2 U)
    (hRU : permutationA0 ≤ U) (g : S)
    (hg : permutationA0.map (MulAut.conj g).toMonoidHom ≤ U) :
    permutationA0.map (MulAut.conj g).toMonoidHom = permutationA0 :=
  SubgroupFusion.weakly_closed_in_p_overgroup_of_one_sylow treeSylow
    permutationA0 U hRU hU radical_weakly_closed_tree g hg

/-- The literal two-residual of the unordered four-block parabolic. -/
@[expose] def blockResidual : Subgroup S :=
  (pResidual 2 fourStabilizer).map fourStabilizer.subtype

private theorem blockResidual_normalized : fourStabilizer ≤ normalizer (blockResidual : Set S) :=
  fourStabilizer.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image fourStabilizer (pResidual 2 fourStabilizer))

private theorem radical_le_blockResidual : permutationA0 ≤ blockResidual := by
  have hR : permutationA0 = fourStabilizer.pCoreIn 2 :=
    permutationA0_eq_kleinGroup.trans fourStabilizer_pCoreIn.symm
  have hRN : fourStabilizer ≤ normalizer (permutationA0 : Set S) := by
    rw [hR]
    exact fourStabilizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image fourStabilizer (pCore 2 fourStabilizer))
  have hN : fourStabilizer ≤ normalizer (permutationA0 ⊓ blockResidual : Set S) :=
    (le_inf hRN blockResidual_normalized).trans inf_normalizer_le_normalizer_inf
  have hi := klein_irreducible (permutationA0 ⊓ blockResidual)
    (inf_le_left.trans_eq permutationA0_eq_kleinGroup) hN
  rcases hi with hz | he
  · have hc : ⁅permutationA0,blockResidual⁆ = ⊥ := by
      apply bot_unique
      have hh : ⁅permutationA0,blockResidual⁆ ≤ permutationA0 ⊓ blockResidual := by
        apply le_inf
        · rw [commutator_comm]
          exact le_normalizer_iff_commutator_le_right.mp
            ((map_subtype_le _).trans hRN)
        · exact le_normalizer_iff_commutator_le_right.mp
            ((hR.le.trans (pCoreIn_le 2 _)).trans blockResidual_normalized)
      exact hh.trans_eq hz
    let c : S := Equiv.swap 0 1 * Equiv.swap 1 2
    have hcH : c ∈ fourStabilizer := by decide +kernel
    have hc3 : (⟨c,hcH⟩ : fourStabilizer)^3 = 1 := by
      apply Subtype.ext
      change (Equiv.swap 0 1 * Equiv.swap 1 2 : S)^3 = 1
      decide +kernel
    have hcX : c ∈ blockResidual := by
      refine ⟨⟨c,hcH⟩,?_,rfl⟩
      exact mem_pResidual_of_orderOf_coprime
        ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc3))
    let r : S := Equiv.swap 0 1 * Equiv.swap 2 3
    have hr : r ∈ permutationA0 := subset_closure (Set.mem_insert _ _)
    have hcomm := commutator_eq_bot_iff_le_centralizer.mp hc hr c hcX
    exact (by decide +kernel : c * r ≠ r * c) hcomm |>.elim
  · rw [←permutationA0_eq_kleinGroup] at he
    exact he.symm.le.trans inf_le_right

/-- The original parabolic residual has exactly the marked Klein-product two-core. -/
theorem blockResidual_core : blockResidual.pCoreIn 2 = permutationA0 := by
  apply le_antisymm
  · have hh := pCoreIn_mono_of_normalizes (p := 2) (map_subtype_le (pResidual 2 fourStabilizer))
      blockResidual_normalized
    rwa [fourStabilizer_pCoreIn,←permutationA0_eq_kleinGroup] at hh
  · apply le_pCoreIn_of_normalizes
    · exact (permutationActor_elementary 0).isPGroup
    · exact radical_le_blockResidual
    · exact (map_subtype_le _).trans normalizer_permutationA0.symm.le

/-- The normalizer of this radical normalizes the literal residual. -/
theorem radical_normalizer_le : normalizer (permutationA0 : Set S) ≤
    normalizer (blockResidual : Set S) := by
  rw [normalizer_permutationA0]
  exact blockResidual_normalized
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi.SymmetricEight
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi.SymmetricEight
open BinaryNaturalDual.FourActors
variable {Q : Type*} [Group Q]

private theorem marking_properties (U X : Subgroup Q) (hU : IsPGroup 2 U)
    (hRU : X.pCoreIn 2 ≤ U) (e : Q ≃* Equiv.Perm (Fin 8))
    (hX : X.map e.toMonoidHom = blockResidual) :
    (∀ g : Q, (X.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ U →
      (X.pCoreIn 2).map (MulAut.conj g).toMonoidHom = X.pCoreIn 2) ∧
    normalizer (X.pCoreIn 2 : Set Q) ≤ normalizer (X : Set Q) := by
  have hR : (X.pCoreIn 2).map e.toMonoidHom = permutationA0 := by
    rw [map_pCoreIn_of_injective 2 _ _ e.injective,hX,blockResidual_core]
  constructor
  · intro g hg
    apply map_injective (f := e.toMonoidHom) e.injective
    have hcomm : ((X.pCoreIn 2).map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
        ((X.pCoreIn 2).map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
    rw [hcomm,hR]
    apply radical_weakly_closed (U.map e.toMonoidHom) (hU.map e.toMonoidHom)
    · rw [←hR]
      exact map_mono hRU
    · have hm := map_mono (f := e.toMonoidHom) hg
      rwa [hcomm,hR] at hm
  · intro g hg
    have hm := mem_map_of_mem e.toMonoidHom hg
    rw [map_equiv_normalizer_eq,hR] at hm
    have hh := radical_normalizer_le hm
    rw [←hX,←map_equiv_normalizer_eq] at hh
    obtain ⟨a,ha,he⟩ := hh
    exact e.injective he ▸ ha
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi.SymmetricEight
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual component quotient admits no S₈ equivalence carrying its
original residual to the literal four-block parabolic residual. -/
theorem doubleNatural_four_pure_component_not_marked_symmetricEight_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          K ∈ cComponentsIn H ∧ K ∈ Chapter1.L G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsQuasisimple (XiQuotient K) ∧
          ((componentOrbit K (T : Subgroup G)).subgroupOf H).Normal ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          componentOrbit V (T : Subgroup G) ⊓
            centralizer (componentOrbit K (T : Subgroup G) : Set G) = ⊥ ∧
          (Alternatives 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K ∨
            HeldAlternative 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K) ∧
          ∃ hn : H ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G),
            let q := PureFourXi.sectionProjection H (componentOrbit K (T : Subgroup G)) hn
            let R := ((X.subgroupOf H).map q).pCoreIn 2
            (normalizer ((B.pointSylow w).subgroupOf H : Set H)).map q =
              normalizer (((B.pointSylow w).subgroupOf H).map q :
                Set (H ⧸ PureFourXi.sectionKernel H (componentOrbit K (T : Subgroup G)) hn)) ∧
            ¬ ((X.subgroupOf H).map q).Normal ∧
            R ≤ ((B.pointSylow w).subgroupOf H).map q ∧
            ¬ ∃ e : (H ⧸ PureFourXi.sectionKernel H (componentOrbit K (T : Subgroup G)) hn) ≃*
                Equiv.Perm (Fin 8),
              ((X.subgroupOf H).map q).map e.toMonoidHom =
                PureFourXi.SymmetricEight.blockResidual := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt,hn,hquot,hnormal,hR,hobs⟩ :=
    D.doubleNatural_four_pure_component_radical_obstruction_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  refine ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt,hn,
    hquot,hnormal,hR,?_⟩
  rintro ⟨e,hmark⟩
  exact hobs (PureFourXi.SymmetricEight.marking_properties _ _
    (T.isPGroup'.comap_subtype.map _)
    (hR.trans (map_mono (comap_mono inf_le_left))) e hmark)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
