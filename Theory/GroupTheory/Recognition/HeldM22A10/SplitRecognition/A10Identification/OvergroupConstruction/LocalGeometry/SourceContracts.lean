module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.Contracts

/-!
# Held's corrected marked six- and seven-point source interfaces

Held's Lemma 4.2 places `π * μ` and `τ * λ` in the subgroup A isomorphic
to A₆. The older `LocalGeometry.SixLocalData` instead contains `π * λ`;
`SixConstruction.not_nonempty_sixLocalData` proves that older interface
inconsistent with its disjointness condition. Its public declarations and
that diagnostic remain unchanged.

The structures in `LocalGeometry.Source` retain every other field of the
older interfaces and replace that one membership by `tau_lam_mem`. The
crossing centralizer and marked S₇ data use this corrected six-point data;
the target `LocalGeometry.CrossingModel` is reused unchanged. These are
explicit intermediate data types. No constructor existence or recognition
theorem is asserted here.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756. The corrected relation is in Lemma 4.2,
printed p.232; the subsequent marked geometry is in §§5.1–5.11.
Conjugation `x^g` in that source means `g⁻¹ * x * g`.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.Source

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

local notation "π" => pi D e
local notation "μ" => mu D e
local notation "μ'" => mu' D e
local notation "τ" => tau D e
local notation "τ'" => tau' D e
local notation "ℓ" => lam D e
local notation "ξ" => xi D e

/-- The marked A₆ and S₆ configuration with Held's `τ * λ ∈ A` relation.
Constructing this data remains a separate source theorem. -/
public structure SixLocalData where
  u : G
  v : G
  A : Subgroup G
  alternatingEquiv : A ≃* alternatingGroup (Fin 6)
  symmetricEquiv : (A ⊔ zpowers μ' : Subgroup G) ≃* Perm (Fin 6)
  u_order : orderOf u = 3
  v_order : orderOf v = 3
  u_v_commute : Commute u v
  mu_u : u⁻¹ * μ * u = ℓ
  lam_u : u⁻¹ * ℓ * u = μ * ℓ
  u_tau'_commute : Commute u τ'
  mu'_u : μ' * u * μ' = u⁻¹
  v_mu_commute : Commute v μ
  v_lam_commute : Commute v ℓ
  v_xi_commute : Commute v ξ
  pi_v : v⁻¹ * π * v = π * τ * ℓ
  tau_v : v⁻¹ * τ * v = π * μ * ℓ
  mu'_v : μ' * v * μ' = v⁻¹
  A_centralizes : A ≤ centralizer ({μ, ℓ} : Set G)
  A_disjoint : Disjoint (closure ({μ, ℓ} : Set G)) A
  mu'_normalizes : μ' ∈ normalizer (A : Set G)
  centralizer_mu : centralizer ({μ} : Set G) =
    (closure ({μ, ℓ} : Set G) ⊔ A) ⊔ zpowers μ'
  pi_mu_mem : π * μ ∈ A
  tau_lam_mem : τ * ℓ ∈ A
  v_mem : v ∈ A
  mu'_xi_mem : μ' * ξ ∈ A
  root_centralizes : ∀ a ∈ A, Commute (u * v) a

@[expose] public def crossingCentralizer (L : SixLocalData D e) : Subgroup G :=
  centralizer ({L.v * μ', π * μ * μ', ξ} : Set G)

/-- The marked S₇ extension over the corrected six-point source data. -/
public structure SevenLocalData (L : SixLocalData D e) where
  embedding : Perm (Fin 7) →* G
  injective : Function.Injective embedding
  six_range : (MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)).map embedding =
    L.A ⊔ zpowers μ'
  six_even_range : (alternatingGroup (Fin 7) ⊓
    MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)).map embedding = L.A
  mark_mu' : embedding (swap 0 1) = μ'
  mark_v_mu' : embedding (swap 1 2) = L.v * μ'
  mark_pi_mu_mu' : embedding (swap 2 3) = π * μ * μ'
  mark_xi : embedding (swap 4 5) = ξ
  root_action : ∀ p, embedding p * (L.u * L.v) * (embedding p)⁻¹ =
    if Equiv.Perm.sign p = 1 then L.u * L.v else (L.u * L.v)⁻¹
  crossingEquiv : crossingCentralizer D e L ≃* CrossingModel

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.Source
