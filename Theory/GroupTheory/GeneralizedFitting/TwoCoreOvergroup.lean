module
public import Theory.GroupTheory.GeneralizedFitting.ComponentOvergroup
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# Two-cores of overgroups of the generalized Fitting subgroup

If O₂(G) is trivial, the two-core of an overgroup of F*(G) is trivial.
Its two-core centralizes the odd-order Fitting subgroup and all ordinary
components. Self-centralization of F*(G) places it in the Fitting subgroup,
where coprimeness forces it to vanish.

This is the two-core comparison used in the contained-Fitting branch of
Aschbacher--Smith C.2.13 and C.4.8, printed pp.148,153.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An overgroup of F*(G) has trivial two-core when G does. -/
theorem twoCore_eq_bot_of_generalizedFitting_le (M : Subgroup G) (hF : generalizedFitting G ≤ M)
    (hcore : pCore 2 G = ⊥) : pCore 2 M = ⊥ := by
  let P := pCore 2 M
  have hFM : fittingSubgroup G ≤ M := (fitting_le_generalizedFitting G).trans hF
  let F := (fittingSubgroup G).subgroupOf M
  have hcop : Nat.Coprime (Nat.card P) (Nat.card F) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    change Nat.Coprime (Nat.card (pCore 2 M)) (Nat.card F)
    rw [hn,Nat.card_congr (subgroupOfEquivOfLe hFM).toEquiv]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)) |>.pow_left n
  have hd : Disjoint P F := disjoint_of_coprime_natCard hcop
  have hPF : P.map M.subtype ≤ centralizer (fittingSubgroup G : Set G) := by
    have hc := commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
    rintro _ ⟨p,hp,rfl⟩ f hf
    exact congrArg Subtype.val (hc hp ⟨f,hFM hf⟩ hf)
  have hPE : P.map M.subtype ≤ centralizer (componentLayer G : Set G) := by
    apply le_centralizer_iff.mpr
    apply sSup_le
    intro K hK
    have hKM : K ≤ M := (component_le_generalizedFitting G K hK).trans hF
    let : Group.IsNilpotent P := pCore_isNilpotent
    have hc := (hK.subgroupOf hKM).le_centralizer_of_solvable_normal P
    intro k hk p hp
    obtain ⟨p,hp,rfl⟩ := hp
    exact congrArg Subtype.val (hc (show (⟨k,hKM hk⟩ : M) ∈ K.subgroupOf M from hk) p hp)
  have hPfit : P.map M.subtype ≤ fittingSubgroup G := by
    apply le_trans _ centralizer_generalizedFitting_le_fitting
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hPF) (le_centralizer_iff.mp hPE)
  have hPF' : P ≤ F := by
    intro p hp
    exact hPfit (mem_map_of_mem M.subtype hp)
  exact le_bot_iff.mp ((le_inf le_rfl hPF').trans hd.le_bot)

end Theory.GroupTheory
