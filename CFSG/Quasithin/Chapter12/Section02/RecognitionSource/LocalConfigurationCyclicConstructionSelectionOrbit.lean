module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionOrbit
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupAction.MaximalCosetOrbit

/-!
# The original pair is the rotation displacement on the canonical orbit

For W = ⟨(O₂(H) ∩ V)^H⟩, the two conjugate axes show [W,I] ≤ U.
Since U = [U,⟨g⟩], this gives [W,I] = [W,⟨g⟩] = U. Coprime action
then splits W into U and the rotation-fixed subgroup. For an inverted
rotation this fixed subgroup is C_W(I), yielding the source direct sum. Centralizers of the
rotation in P preserve U, so the Frattini subgroup preserves U in the
extraspecial case.

These are the pair-module identities used in invariant Sylow selection;
the source application is LocalConfigurationCyclicConstructionSelectionAssembly.
Source: Aschbacher–Smith, 12.2.21–22, printed pp.802–803.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g v : G}

omit [Finite G] in
/-- The pair core is precisely the displacement of W by the pair or its rotation. -/
theorem CyclicConstructionSeed.orbit_commutator_pair
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ⁅componentOrbit (H.pCoreIn 2 ⊓ V) H, cyclicPairJoin (zpowers g) U V⁆ = U ∧
      ⁅componentOrbit (H.pCoreIn 2 ⊓ V) H, zpowers g⁆ = U := by
  let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
  let I := cyclicPairJoin (zpowers g) U V
  let B := V.map (MulAut.conj g).toMonoidHom
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  have hUH : U ≤ W := (le_componentOrbit U P).trans_eq (S.orbit_eq D A hTV).symm
  have hIn : I ≤ normalizer (U : Set G) := by
    rw [← S.pair_core]
    exact I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hgI : zpowers g ≤ I := le_sup_left.trans le_sup_left
  have hgW : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_componentOrbit _ _ (hPH S.generator_mem))
  have hgU : U.map (MulAut.conj g).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (hIn (hgI (mem_zpowers g)))
  have hWV : ⁅W, V⁆ ≤ U := (S.orbit_transvections D A hTV).le.trans inf_le_left
  have hWB : ⁅W, B⁆ ≤ U := by
    rw [← hgW, ← map_commutator, ← hgU]
    exact map_mono hWV
  have hWI : ⁅W, I⁆ ≤ U := by
    rw [commutator_comm]
    change ⁅cyclicPairJoin (zpowers g) U V, W⁆ ≤ U
    rw [S.pair_generated]
    exact commutator_sup_le_of_relative_normal I V B W U hIn
      (show V ≤ I from le_sup_right)
      (le_sup_right.trans S.pair_generated.ge)
      (by rwa [commutator_comm]) (by rwa [commutator_comm])
  have hg : ⁅W, zpowers g⁆ = U := le_antisymm
    ((commutator_mono le_rfl hgI).trans hWI)
    (by rw [← S.core_moved]; exact commutator_mono hUH le_rfl)
  exact ⟨le_antisymm hWI (hg.ge.trans (commutator_mono le_rfl hgI)), hg⟩


/-- Coprime action splits the canonical orbit into the pair core and rotation-fixed part. -/
theorem CyclicConstructionSeed.orbit_split_rotation
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
    W = U ⊔ (W ⊓ centralizer (zpowers g : Set G)) ∧
      Disjoint U (W ⊓ centralizer (zpowers g : Set G)) := by
  let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
  let : Fact p.Prime := ⟨S.prime⟩
  let : IsElementaryAbelian 2 W := S.orbit_elementary D hTV hTI
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  have hn : zpowers g ≤ normalizer (W : Set G) :=
    (zpowers_le.mpr S.generator_mem).trans (hPH.trans (le_normalizer_componentOrbit _ _))
  have hc : Nat.Coprime (Nat.card (zpowers g)) (Nat.card W) := by
    obtain ⟨a, ha⟩ := (S.pgroup.to_le (zpowers_le.mpr S.generator_mem)).exists_card_eq
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [ha, hb]
    exact S.odd_prime.coprime_two_right.pow a b
  have hm : ⁅W, zpowers g⁆ = U := (S.orbit_commutator_pair D A hTV).2
  constructor
  · simpa only [hm] using eq_commutator_sup_centralizer_of_solvable_coprime W
      (zpowers g) hn (Group.isSolvable_of_comm fun x y => mul_comm x y) hc
  · simpa only [hm] using commutator_disjoint_centralizer_of_coprime W (zpowers g) hn hc


omit [Finite G] in
/-- The rotation centralizer in P preserves its actual displacement subgroup U. -/
theorem CyclicConstructionSeed.rotation_centralizer_normalizes_core
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    P ⊓ centralizer (zpowers g : Set G) ≤ normalizer (U : Set G) := by
  let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  intro x hx
  have hxW : W.map (MulAut.conj x).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit _ _ (hPH hx.1))
  have hxg : (zpowers g).map (MulAut.conj x).toMonoidHom = zpowers g :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) hx.2)
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hm : ⁅W, zpowers g⁆ = U := (S.orbit_commutator_pair D A hTV).2
  rw [← hm, map_commutator]
  exact congrArg₂ (fun B C : Subgroup G => ⁅B, C⁆) hxW hxg


/-- In the extraspecial branch, the literal embedded Frattini subgroup normalizes U. -/
theorem CyclicConstructionSeed.frattini_normalizes_core_of_extraspecial
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P) :
    (frattini P).map P.subtype ≤ normalizer (U : Set G) := by
  let : Fact p.Prime := ⟨S.prime⟩
  let : IsExtraspecial p P := he
  apply le_trans ?_ (S.rotation_centralizer_normalizes_core D A hTV)
  refine le_inf (map_subtype_le _) ?_
  rintro x ⟨a, ha, rfl⟩
  rw [IsExtraspecial.frattini_eq_center (p := p)] at ha
  apply mem_centralizer_iff.mpr
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp ha
    (⟨y, (zpowers_le.mpr S.generator_mem) hy⟩ : P))

/-- The rotation-fixed subgroup of W is fixed by the whole original pair. -/
theorem CyclicConstructionSeed.orbit_fixed_pair
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (hv : v ∈ V) (hvU : v ∉ U) (hinv : v * g * v⁻¹ = g⁻¹) :
    let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
    W ⊓ centralizer (zpowers g : Set G) =
      W ⊓ centralizer (cyclicPairJoin (zpowers g) U V : Set G) := by
  let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
  let C := W ⊓ centralizer (zpowers g : Set G)
  let I := cyclicPairJoin (zpowers g) U V
  let : IsElementaryAbelian 2 W := S.orbit_elementary D hTV hTI
  have hUW : U ≤ W := (le_componentOrbit U P).trans_eq (S.orbit_eq D A hTV).symm
  have hvW : v ∈ normalizer (W : Set G) :=
    le_normalizer_componentOrbit _ _ (S.hstar.1.1.2 (D.le_sylow hv))
  have hvg : v ∈ normalizer (zpowers g : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (v * g * v⁻¹) = zpowers g
    rw [hinv, zpowers_inv]
  have hvC : v ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hvW, normalizer_le_normalizer_centralizer _ hvg⟩
  have hcommC : ⁅C, zpowers v⁆ ≤ C :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hvC)
  have hcommU : ⁅C, zpowers v⁆ ≤ U :=
    (commutator_mono inf_le_left (zpowers_le.mpr hv)).trans
      ((S.orbit_transvections D A hTV).le.trans inf_le_left)
  have hzero : ⁅C, zpowers v⁆ = ⊥ := bot_unique
    ((le_inf hcommU hcommC).trans (S.orbit_split_rotation D A hTV hTI).2.le_bot)
  have hvfix : zpowers v ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hUfix : U ≤ centralizer (C : Set G) := by
    intro u hu c hc
    exact le_centralizer W (hUW hu) c hc.1
  have hVfix : V ≤ centralizer (C : Set G) := by
    rw [← sup_zpowers_eq_of_relIndex_prime (inf_le_right : U ⊓ V ≤ V)
      Nat.prime_two S.hyperplane_index hv (fun hh => hvU hh.1)]
    exact sup_le (inf_le_left.trans hUfix) hvfix
  have hIfix : I ≤ centralizer (C : Set G) := sup_le
    (sup_le (le_centralizer_iff.mp inf_le_right) hUfix) hVfix
  apply le_antisymm
  · exact le_inf inf_le_left (le_centralizer_iff.mp hIfix)
  · exact inf_le_inf_left _ (centralizer_le (le_sup_left.trans le_sup_left : zpowers g ≤ I))


/-- The actual splitting W = U ⊕ C_W(I), with the literal pair I. -/
theorem CyclicConstructionSeed.orbit_split_pair
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (hv : v ∈ V) (hvU : v ∉ U) (hinv : v * g * v⁻¹ = g⁻¹) :
    let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
    W = U ⊔ (W ⊓ centralizer (cyclicPairJoin (zpowers g) U V : Set G)) ∧
      Disjoint U (W ⊓ centralizer (cyclicPairJoin (zpowers g) U V : Set G)) := by
  simpa only [S.orbit_fixed_pair D A hTV hTI hv hvU hinv] using
    S.orbit_split_rotation D A hTV hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
