module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanVanishing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Transport

/-!
# Symmetric reverse residual

The nonsolvable `b = 2` Cartan residual argument is equivariant under the
local transporter.  Applying the existing path residual theorem to the
translated reversed critical pair gives the opposite orientation: a local
transporter sends `β` to the selected neighbor and its residual is nontrivial
while disjoint from the prescribed terminal `Q`-core.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.8), pp.160--161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

private theorem residual_translate (h : HypothesisF11 L S)
    (g : G₀ L S) (m t w z : Vertex F) :
    bTwoResidual F (g • m) (g • t) (g • w) (g • z) =
      (bTwoResidual F m t w z).map (MulAut.conj g).toMonoidHom := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  rw [bTwoResidual, bTwoResidual, D_translate, Z_translate, Z_translate,
    ← Subgroup.map_sup, map_inf_centralizer_of_injective _ (MulAut.conj g).injective]

theorem original_bTwo_reverse_residual_trivial
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g ∈ graphLocalGroup F u, g • β = y ∧
      bTwoResidual F β y α (g • α) ≠ ⊥ ∧
      bTwoResidual F β y α (g • α) ⊓ Q F t = ⊥ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g₀,hg₀,hg₀K,hg₀t,a,ha,haK,hau,
    hW₀,hR₀,hdec₀,hdis₀,hdisu₀,hKn₀,hRC₀,hJC₀,hthree₀,hconj₀,hRne₀,hzero₀⟩ :=
    original_bTwo_path_cartan_residual_trivial h hc hne hb hβu ht htne hy hyne hns
  have hab : a • β = β := sylowGenerated_le _ ha
  have hab' : a⁻¹ • β = β := by simpa only [hab] using inv_smul_smul a β
  have hau' : a⁻¹ • u = α := by rw [← hau, inv_smul_smul]
  have hrev := graph_criticalPair_reverse H (reduced_kernel_sylow h) hc hne
  have hc' : IsCriticalPair F α (a⁻¹ • α) := by
    simpa only [hau'] using CommutingNontrivial.criticalPair_translate F hrev a⁻¹
  have hn' : ⁅Z F α,Z F (a⁻¹ • α)⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map (MulAut.conj a).toMonoidHom) hz
    rw [map_commutator, ← Z_translate, ← Z_translate, smul_inv_smul,
      hau, Subgroup.map_bot, commutator_comm] at hh
    exact hne hh
  have adj (v w : Vertex F) (hvw : (graph F).Adj v w) :
      (graph F).Adj (a⁻¹ • v) (a⁻¹ • w) :=
    (Subgroup.CosetGeometry.translationGraphIso F a⁻¹).map_adj_iff.mpr hvw
  have hm' : (graph F).Adj β (a⁻¹ • α) := by
    simpa only [hab'] using adj β α (by exact ⟨by change true ≠ false; decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩)
  have ht' : (graph F).Adj α (a⁻¹ • y) := by simpa only [hau'] using adj u y hy
  have htne' : a⁻¹ • y ≠ β := by
    intro he
    apply hyne
    have hh := congrArg (a • ·) he
    simpa only [smul_inv_smul,hab] using hh
  have hy' : (graph F).Adj (a⁻¹ • α) (a⁻¹ • t) := adj α t ht
  have hyne' : a⁻¹ • t ≠ β := by
    intro he
    apply htne
    have hh := congrArg (a • ·) he
    simpa only [smul_inv_smul,hab] using hh
  obtain ⟨C,hCfix,hCd,hCgen,hCo,hCcomm,hCprod,b,hbmem,hbC,hbmove,
      c,hcmem,hcC,hcmove,hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
    original_bTwo_path_cartan_residual_trivial h hc' hn' hb hm' ht' htne' hy' hyne' hns
  let g := a * b * a⁻¹
  have hgm : g ∈ graphLocalGroup F u := by
    have hh : g ∈ (graphLocalGroup F α).map (MulAut.conj a).toMonoidHom :=
      ⟨b,hbmem,rfl⟩
    have he := graphLocalGroup_conjugate H a α
    rw [hau] at he
    exact he.symm ▸ hh
  have hgmove : g • β = y := by
    change (a * b * a⁻¹) • β = y
    rw [mul_smul,mul_smul,hab',hbmove,smul_inv_smul]
  have hmap : (bTwoResidual F β (a⁻¹ • y) (a⁻¹ • α)
      (b • (a⁻¹ • α))).map (MulAut.conj a).toMonoidHom =
      bTwoResidual F β y α (g • α) := by
    rw [← residual_translate h,hab,smul_inv_smul,smul_inv_smul]
    change bTwoResidual F β y α (a • b • a⁻¹ • α) = _
    rw [show g • α = a • b • a⁻¹ • α by simp only [g,mul_smul]]
  refine ⟨g,hgm,hgmove,?_,?_⟩
  · intro hz
    apply hRne
    apply (map_eq_bot_iff_of_injective (f := (MulAut.conj a).toMonoidHom) _ (MulAut.conj a).injective).mp
    exact hmap.trans hz
  · have hh := congrArg (map (MulAut.conj a).toMonoidHom) hzero
    rw [map_inf _ _ _ (MulAut.conj a).injective,hmap,← Q_translate,
      smul_inv_smul,Subgroup.map_bot] at hh
    exact hh


/-- The symmetric Cartan construction retains the four-core decomposition of
its transported residual.  In particular, the reverse residual lies in both
additional endpoint cores needed by the reverse six-path argument. -/
theorem original_bTwo_reverse_residual_four_core_cartan
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g ∈ graphLocalGroup F u, g • β = y ∧
      bTwoResidual F β y α (g • α) =
        (D F β y ⊓ Q F α) ⊓ Q F (g • α) ∧
      bTwoResidual F β y α (g • α) ≠ ⊥ ∧
      bTwoResidual F β y α (g • α) ⊓ Q F t = ⊥ ∧
      ∃ K : Subgroup (G₀ L S),
        g ∈ normalizer (K : Set (G₀ L S)) ∧
        K ≤ stabilizer F (g • t) ⊓ stabilizer F (g • α) ⊓
          stabilizer F y ⊓ stabilizer F u ⊓ stabilizer F β ⊓
          stabilizer F α ⊓ stabilizer F t ∧
        K ⊔ (stabilizer F t ⊓ stabilizer F α).pCoreIn 2 =
          stabilizer F t ⊓ stabilizer F α := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g₀,hg₀,hg₀K,hg₀t,a,ha,haK,hau,
    hW₀,hR₀,hdec₀,hdis₀,hdisu₀,hKn₀,hRC₀,hJC₀,hthree₀,hconj₀,hRne₀,hzero₀⟩ :=
    original_bTwo_path_cartan_residual_trivial h hc hne hb hβu ht htne hy hyne hns
  have hab : a • β = β := sylowGenerated_le _ ha
  have hab' : a⁻¹ • β = β := by simpa only [hab] using inv_smul_smul a β
  have hau' : a⁻¹ • u = α := by rw [← hau, inv_smul_smul]
  have hrev := graph_criticalPair_reverse H (reduced_kernel_sylow h) hc hne
  have hc' : IsCriticalPair F α (a⁻¹ • α) := by
    simpa only [hau'] using CommutingNontrivial.criticalPair_translate F hrev a⁻¹
  have hn' : ⁅Z F α,Z F (a⁻¹ • α)⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map (MulAut.conj a).toMonoidHom) hz
    rw [map_commutator, ← Z_translate, ← Z_translate, smul_inv_smul,
      hau, Subgroup.map_bot, commutator_comm] at hh
    exact hne hh
  have adj (v w : Vertex F) (hvw : (graph F).Adj v w) :
      (graph F).Adj (a⁻¹ • v) (a⁻¹ • w) :=
    (Subgroup.CosetGeometry.translationGraphIso F a⁻¹).map_adj_iff.mpr hvw
  have hm' : (graph F).Adj β (a⁻¹ • α) := by
    simpa only [hab'] using adj β α (by exact ⟨by change true ≠ false; decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩)
  have ht' : (graph F).Adj α (a⁻¹ • y) := by simpa only [hau'] using adj u y hy
  have htne' : a⁻¹ • y ≠ β := by
    intro he
    apply hyne
    have hh := congrArg (a • ·) he
    simpa only [smul_inv_smul,hab] using hh
  have hy' : (graph F).Adj (a⁻¹ • α) (a⁻¹ • t) := adj α t ht
  have hyne' : a⁻¹ • t ≠ β := by
    intro he
    apply htne
    have hh := congrArg (a • ·) he
    simpa only [smul_inv_smul,hab] using hh
  obtain ⟨C,hCfix,hCd,hCgen,hCo,hCcomm,hCprod,b,hbmem,hbC,hbmove,
      c,hcmem,hcC,hcmove,hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
    original_bTwo_path_cartan_residual_trivial h hc' hn' hb hm' ht' htne' hy' hyne' hns
  let g := a * b * a⁻¹
  have hgm : g ∈ graphLocalGroup F u := by
    have hh : g ∈ (graphLocalGroup F α).map (MulAut.conj a).toMonoidHom :=
      ⟨b,hbmem,rfl⟩
    have he := graphLocalGroup_conjugate H a α
    rw [hau] at he
    exact he.symm ▸ hh
  have hgmove : g • β = y := by
    change (a * b * a⁻¹) • β = y
    rw [mul_smul,mul_smul,hab',hbmove,smul_inv_smul]
  have hmap : (bTwoResidual F β (a⁻¹ • y) (a⁻¹ • α)
      (b • (a⁻¹ • α))).map (MulAut.conj a).toMonoidHom =
      bTwoResidual F β y α (g • α) := by
    rw [← residual_translate h,hab,smul_inv_smul,smul_inv_smul]
    change bTwoResidual F β y α (a • b • a⁻¹ • α) = _
    rw [show g • α = a • b • a⁻¹ • α by simp only [g,mul_smul]]
  let φ := (MulAut.conj a).toMonoidHom
  let E := stabilizer F α ⊓ stabilizer F β
  let E' := stabilizer F u ⊓ stabilizer F β
  let K := C.map φ
  have hCy : C ≤ stabilizer F (a⁻¹ • y) := fun z hz => (hCfix hz).1.1.1.1
  have hCu : C ≤ stabilizer F α := fun z hz => (hCfix hz).1.1.1.2
  have hCβ : C ≤ stabilizer F β := fun z hz => (hCfix hz).1.1.2
  have hCα : C ≤ stabilizer F (a⁻¹ • α) := fun z hz => (hCfix hz).1.2
  have hCt : C ≤ stabilizer F (a⁻¹ • t) := fun z hz => (hCfix hz).2
  have hmapInv (v : Vertex F) :
      (stabilizer F (a⁻¹ • v)).map φ = stabilizer F v := by
    rw [stabilizer_translate, Subgroup.map_map]
    have hconj : φ.comp (MulAut.conj a⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro z
      simp [φ, MulAut.conj_apply, mul_assoc]
    rw [hconj]
    simp
  have hKy : K ≤ stabilizer F y := by
    have hh : C.map φ ≤ (stabilizer F (a⁻¹ • y)).map φ := map_mono hCy
    rw [hmapInv] at hh
    exact hh
  have hKu : K ≤ stabilizer F u := by
    have hh : C.map φ ≤ (stabilizer F α).map φ := map_mono hCu
    rw [← stabilizer_translate, hau] at hh
    exact hh
  have hKβ : K ≤ stabilizer F β := by
    have hh : C.map φ ≤ (stabilizer F β).map φ := map_mono hCβ
    rw [← stabilizer_translate, hab] at hh
    exact hh
  have hKα : K ≤ stabilizer F α := by
    have hh : C.map φ ≤ (stabilizer F (a⁻¹ • α)).map φ := map_mono hCα
    rw [hmapInv] at hh
    exact hh
  have hKt : K ≤ stabilizer F t := by
    have hh : C.map φ ≤ (stabilizer F (a⁻¹ • t)).map φ := map_mono hCt
    rw [hmapInv] at hh
    exact hh
  have hmapE : E.map φ = E' := by
    dsimp [E, E']
    rw [map_inf _ _ _ (MulAut.conj a).injective, ← stabilizer_translate,
      ← stabilizer_translate, hau, hab]
  have hmapCore : (E.pCoreIn 2).map φ = E'.pCoreIn 2 := by
    rw [← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 φ (MulAut.conj a).injective, hmapE]
  have hKgen : K ⊔ E'.pCoreIn 2 = E' := by
    have hh := congrArg (Subgroup.map φ) hCgen
    rw [Subgroup.map_sup, hmapCore, hmapE] at hh
    exact hh
  have hKdis : Disjoint K (E'.pCoreIn 2) := by
    have hh := Subgroup.disjoint_map (f := φ) (MulAut.conj a).injective hCd
    rw [hmapCore] at hh
    simpa only [K] using hh
  have hoK : Odd (Nat.card K) := by
    dsimp [K]
    rw [card_map_of_injective (MulAut.conj a).injective]
    exact hCo
  obtain ⟨_, hgenTarget⟩ :=
    CommutingTrivial.path_cartan_complement_at_edge H hβu.symm ht.symm K
      (le_inf hKu hKβ) (le_inf hKt hKα) hoK hKdis hKgen
  have hbmap : C.map (MulAut.conj b).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp hbC
  have hbmap' : C.map (↑(MulAut.conj b) : (G₀ L S) →* (G₀ L S)) = C := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using hbmap
  have hKmapg : K.map (MulAut.conj g).toMonoidHom = K := by
    dsimp [K, φ]
    rw [Subgroup.map_map]
    have hcomp :
        (↑(MulAut.conj g) : (G₀ L S) →* (G₀ L S)).comp
            (↑(MulAut.conj a) : (G₀ L S) →* (G₀ L S)) =
          (↑(MulAut.conj a) : (G₀ L S) →* (G₀ L S)).comp
            (↑(MulAut.conj b) : (G₀ L S) →* (G₀ L S)) := by
      ext z
      simp [g, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, hbmap']
  have hgK : g ∈ normalizer (K : Set (G₀ L S)) :=
    mem_normalizer_iff_map_conj_eq.mpr hKmapg
  have htransport (v : Vertex F) (hv : K ≤ stabilizer F v) :
      K ≤ stabilizer F (g • v) := by
    have hh : K.map (MulAut.conj g).toMonoidHom ≤
        (stabilizer F v).map (MulAut.conj g).toMonoidHom := map_mono hv
    rw [hKmapg] at hh
    rw [stabilizer_translate]
    exact hh
  have hKgT := htransport t hKt
  have hKgα := htransport α hKα
  have hKall' : K ≤ stabilizer F (g • t) ⊓ (stabilizer F (g • α) ⊓
      (stabilizer F y ⊓ (stabilizer F u ⊓ (stabilizer F β ⊓
        (stabilizer F α ⊓ stabilizer F t))))) :=
    le_inf hKgT (le_inf hKgα (le_inf hKy
      (le_inf hKu (le_inf hKβ (le_inf hKα hKt)))))
  have hKall : K ≤ stabilizer F (g • t) ⊓ stabilizer F (g • α) ⊓
      stabilizer F y ⊓ stabilizer F u ⊓ stabilizer F β ⊓
      stabilizer F α ⊓ stabilizer F t := by
    simpa only [inf_assoc] using hKall'
  refine ⟨g,hgm,hgmove,?_,?_,?_,?_⟩
  · have hh := congrArg (map (MulAut.conj a).toMonoidHom) hR
    rw [map_inf _ _ _ (MulAut.conj a).injective,
      map_inf _ _ _ (MulAut.conj a).injective,
      ← D_translate, ← Q_translate, ← Q_translate,
      smul_inv_smul, smul_inv_smul, hab, hmap] at hh
    simpa only [g, mul_smul] using hh
  · intro hz
    apply hRne
    apply (map_eq_bot_iff_of_injective (f := (MulAut.conj a).toMonoidHom) _ (MulAut.conj a).injective).mp
    exact hmap.trans hz
  · have hh := congrArg (map (MulAut.conj a).toMonoidHom) hzero
    rw [map_inf _ _ _ (MulAut.conj a).injective,hmap,← Q_translate,
      smul_inv_smul,Subgroup.map_bot] at hh
    exact hh
  · exact ⟨K,hgK,hKall,hgenTarget⟩


/-- The reverse residual is the intersection of the four source cores. -/
theorem original_bTwo_reverse_residual_four_core
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g ∈ graphLocalGroup F u, g • β = y ∧
      bTwoResidual F β y α (g • α) =
        (D F β y ⊓ Q F α) ⊓ Q F (g • α) ∧
      bTwoResidual F β y α (g • α) ≠ ⊥ ∧
      bTwoResidual F β y α (g • α) ⊓ Q F t = ⊥ := by
  obtain ⟨g, hg, hgy, hR, hRne, hRzero, _⟩ :=
    original_bTwo_reverse_residual_four_core_cartan h hc hne hb hβu ht htne hy hyne hns
  exact ⟨g, hg, hgy, hR, hRne, hRzero⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
