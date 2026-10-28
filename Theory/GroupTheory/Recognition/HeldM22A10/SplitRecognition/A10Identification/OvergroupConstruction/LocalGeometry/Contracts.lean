module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.Coordinates
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Geometric inputs to Held's marked generator construction

`SixLocalData` is the compatible A6 and S6 configuration of Held 4.1--4.2,
after the choice of commuting u,v in 5.1 and the centralization in 5.2.
All subgroups are actual subgroups of G, both small-group identifications are
multiplicative equivalences, and normalization is relative to A.

`SevenLocalData` describes the subsequent S7 embedding (5.4--5.10), with the
original S6 as a point stabilizer and A as its even subgroup. The four marked
transpositions form a path of length three and a disjoint edge. Its final
field is an equivalence for the full ambient intersection of three
centralizers, proved in the first part of 5.11: it is C2 x S3.

These are explicit intermediate hypotheses, not existence theorems. The
marked-generator assembly must construct both inputs from LocalData and its
two stated local hypotheses before claiming the unconditional result.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, pp.232--239. Conjugation x^g means g^-1*x*g.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

local notation "π" => pi D e
local notation "μ" => mu D e
local notation "μ'" => mu' D e
local notation "τ" => tau D e
local notation "τ'" => tau' D e
local notation "ℓ" => lam D e
local notation "ξ" => xi D e

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
  pi_lam_mem : π * ℓ ∈ A
  v_mem : v ∈ A
  mu'_xi_mem : μ' * ξ ∈ A
  root_centralizes : ∀ a ∈ A, Commute (u * v) a

public abbrev CrossingModel := Multiplicative (ZMod 2) × Perm (Fin 3)

@[expose] public def crossingCentralizer (L : SixLocalData D e) : Subgroup G :=
  centralizer ({L.v * μ', π * μ * μ', ξ} : Set G)

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

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
