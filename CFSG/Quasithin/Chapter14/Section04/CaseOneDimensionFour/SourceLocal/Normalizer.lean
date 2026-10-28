module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.ResidualNine

/-!
# The ambient normalizer in the order-32 source branch

The centralizer of V acts on U fixing the elementary eight V pointwise, so
its action has exponent two modulo O₂(H). It is therefore a two-group.
Its normality in N_G(L) puts it in the original Sylow subgroup T. Since L
induces the full automorphism group on V, this gives N_G(L)=LT. The residual
and Sylow supplement also gives the literal ambient identity H=O²(H)T.

These prove the two normalizer factorizations in source 14.4.4(7), retaining
the actual flag and earlier source inputs. The stronger L=N_G(L), core
identity and fusion argument of 14.4.5 remain with qt-d-14414-g2-source.

Source: Aschbacher–Smith, 14.4.4(7), printed p.1007.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_seed_centralizer_le_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    centralizer (V : Set G) ≤ (T : Subgroup G) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  let M := normalizer (L : Set G)
  let C := centralizer (V : Set G)
  have hCM : C ≤ M := H.seed_centralizer_le previous.structural previous.uniqueness
  have hCH : C ≤ F.H := (centralizer_le (F.le_seed 1)).trans
    (Subgroup.centralizer_le_normalizer _)
  have hMN : M ≤ normalizer (V : Set G) := source_normalizer_le_seed_normalizer
    d earlier hq chosen previous.structural previous.alternatives F hne hZ hcard
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let E := V.subgroupOf F.U
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVU
  have hc : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans
    (by simpa [F.last] using F.card 3 (by decide))
  have hp : IsPGroup 2 C := by
    intro x
    let y : F.H := ⟨x, hCH x.property⟩
    have hsquare : (F.uAction y) ^ 2 = 1 := q.square_eq_one_of_fixes_eight E hc _ (by
      intro v hv
      apply Subtype.ext
      change (x : G) * (v : G) * (x : G)⁻¹ = v
      rw [← x.property v hv, mul_inv_cancel_right])
    have hy2 : y ^ 2 ∈ pCore 2 F.H := by
      rw [← source_uhat_kernel d earlier hq chosen previous F hZ]
      change quotientAut (center F.U) (F.uAction (y ^ 2)) = 1
      rw [map_pow, hsquare, map_one]
    obtain ⟨n, hn⟩ := pCore_isPGroup.exists_pow_pow_eq_one (⟨y ^ 2, hy2⟩ : pCore 2 F.H)
    refine ⟨n + 1, Subtype.ext ?_⟩
    have he : ((x : G) ^ 2) ^ (2 ^ n) = 1 :=
      congrArg (fun z : pCore 2 F.H => (z.val : G)) hn
    change (x : G) ^ (2 ^ (n + 1)) = 1
    rw [pow_succ, Nat.mul_comm, pow_mul]
    exact he
  have hcore : C ≤ M.pCoreIn 2 := le_pCoreIn_of_normalizes hp hCM
    (hMN.trans (normalizer_le_normalizer_centralizer V))
  have hTM : (T : Subgroup G) ≤ M := H.sylow_normalizes previous.structural
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := (pCore_isPGroup (p := 2) (G := M)).le_sylow_of_normal (T.subtype hTM)
    rintro x ⟨y,hy,rfl⟩
    exact hh hy
  exact hcore.trans hcoreT

theorem source_normalizer_eq_join (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hMV := source_normalizer_le_seed_normalizer d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  have hCT := source_seed_centralizer_le_sylow d earlier hq chosen previous F hne hZ hcard
  apply le_antisymm _ (sup_le L.le_normalizer (H.sylow_normalizes previous.structural))
  intro m hm
  obtain ⟨l,hl,he⟩ := H.full_L_action (V.normalizerMonoidHom ⟨m,hMV hm⟩)
  have hc : l⁻¹ * m ∈ centralizer (V : Set G) := by
    intro v hv
    have hv' := he (⟨v,hv⟩ : V)
    change l * v * l⁻¹ = m * v * m⁻¹ at hv'
    calc
      v * (l⁻¹ * m) = l⁻¹ * (l * v * l⁻¹) * m := by group
      _ = l⁻¹ * (m * v * m⁻¹) * m := by rw [hv']
      _ = (l⁻¹ * m) * v := by group
  have hx := (L ⊔ (T : Subgroup G)).mul_mem (mem_sup_left hl) (mem_sup_right (hCT hc))
  simpa only [mul_inv_cancel_left] using hx

theorem source_normalizer_factors (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      F.H = (pResidual 2 F.H).map F.H.subtype ⊔ (T : Subgroup G) := by
  refine ⟨source_normalizer_eq_join d earlier hq chosen previous F hne hZ hcard, ?_⟩
  let P : Sylow 2 F.H := T.subtype (F.invariant 1)
  calc
    F.H = (⊤ : Subgroup F.H).map F.H.subtype := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    _ = (pResidual 2 F.H ⊔ (P : Subgroup F.H)).map F.H.subtype :=
      congrArg (Subgroup.map F.H.subtype) (pResidual_sup_sylow_eq_top P).symm
    _ = (pResidual 2 F.H).map F.H.subtype ⊔
        (P : Subgroup F.H).map F.H.subtype := Subgroup.map_sup _ _ _
    _ = (pResidual 2 F.H).map F.H.subtype ⊔ (T : Subgroup G) := by
      change (pResidual 2 F.H).map F.H.subtype ⊔
        ((T : Subgroup G).subgroupOf F.H).map F.H.subtype = _
      exact congrArg ((pResidual 2 F.H).map F.H.subtype ⊔ ·)
        (map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1))
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
