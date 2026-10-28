module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingGeneratedCoreSource
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.InvariantSubgroup
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# The original maximal local core when the block centralizer is trivial

The full orthogonal action makes the image of O2(M) in P/Z(P) either zero
or the whole space. Characteristic two places Z(P) in O2(M) and excludes
the central alternative. Consequently O2(M)=P. The center of P has order
two, so M centralizes it; the reverse inclusion is the original unique
maximal two-local centralizer bound.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_maximal_core_of_centralizer_bot
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    M.pCoreIn 2 = P ∧ M = centralizer ((center P).map P.subtype : Set G) := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let E := P ⊔ D
  let F := K ⊔ (T : Subgroup G)
  let A := M.pCoreIn 2
  let Z := (center P).map P.subtype
  have hEP : E=P := by change P ⊔ D=P; rw [show D=⊥ from hD,sup_bot_eq]
  have hFM : F≤M := sup_le ((map_subtype_le _).trans inf_le_left) hTM
  have hPF : P≤F := (pCoreIn_le 2 K).trans le_sup_left
  have hPM : P≤M := hPF.trans hFM
  have hZP : Z≤P := map_subtype_le _
  have hAP : A≤P := by
    have hh := (d.single_alternating_generated_core hG T hM hTM hu hST hsingle hA).2
    simpa only [hD,sup_bot_eq] using hh
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  change M ⊓ centralizer (A : Set G) ≤ A at hMe
  have hZC : Z≤centralizer (P : Set G) := by
    rintro z ⟨z,hz,rfl⟩
    intro p hp
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨p,hp⟩)
  have hZA : Z≤A := (le_inf (hZP.trans hPM) (hZC.trans (centralizer_le hAP))).trans hMe
  obtain ⟨hd,hp,eE,hn,hfull⟩ := d.single_alternating_whole_square_action hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 D := hd
  let f : F →* MulAut E := E.normalizerMonoidHom.comp (inclusion hn)
  have hAE : A≤E := hAP.trans hEP.ge
  have hFA : F≤normalizer (A : Set G) := hFM.trans (M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  have hAi : ∀t:F,∀x∈A.subgroupOf E,f t x∈A.subgroupOf E := by
    intro t x hx
    exact (mem_normalizer_iff.mp (hFA t.property) x.val).mp hx
  have hcen : (center E).map E.subtype=Z := by
    dsimp [Z]
    rw [hEP]
  have hAEq : A=E := by
    rcases hp.centralFactor_invariant_subgroup eE f
      (MonoidHom.range_eq_top.mp hfull) (A.subgroupOf E) hAi with hc | hc
    · have hAZ : A≤Z := by
        have hh := map_mono (f:=E.subtype) hc
        rwa [map_subgroupOf_eq_of_le hAE,hcen] at hh
      have hPA : P≤A := (le_inf hPM ((le_centralizer_iff.mp hZC).trans
        (centralizer_le hAZ))).trans hMe
      have hPZ : P=Z := le_antisymm (hPA.trans hAZ) hZP
      have hh : Nat.card P=2 := by rw [hPZ,card_map_of_injective P.subtype_injective,hp.center_card]
      have hh' : Nat.card P=32 := hp.card
      omega
    · have hh := congrArg (map E.subtype) hc
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAE,hcen,←MonoidHom.range_eq_map,
        range_subtype,sup_eq_left.mpr hZA] at hh
      exact hh
  have hcore : M.pCoreIn 2=P := hAEq.trans hEP
  refine ⟨hcore,le_antisymm ?_ (d.single_alternating_core_center_centralizer_le hG T hM hTM hu hST hsingle hA)⟩
  have hMP : M≤normalizer (P : Set G) := by
    rw [←hcore]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hMZ : M≤normalizer (Z : Set G) := hMP.trans (normalizer_le_normalizer_characteristic_image P (center P))
  exact hMZ.trans (normalizer_le_centralizer_of_card_two Z (by
    rw [card_map_of_injective P.subtype_injective,hp.center_card]))
end CFSG.Quasithin.Chapter2
