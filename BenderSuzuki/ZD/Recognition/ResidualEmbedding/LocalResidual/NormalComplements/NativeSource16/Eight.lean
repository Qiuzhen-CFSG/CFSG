module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne
public import Theory.GroupTheory.InvolutionCentralizerRank.Fusion

/-!
# The elementary eight and nonsolvable circles in Section 16

The selected involution in D is not distinguished, whereas a distinguished
involution exists in M. The two are not conjugate, so the proved simple-group
form of GLS4 Chapter 1, Lemma 4.10 gives an elementary eight in its centralizer.
Sylow conjugacy moves this eight into the Sylow subgroup already selected
inside M. This discharges the remaining rank-theorem input to Lemma 16.3.

Source: GLS IV, Chapter 2, Lemma 16.3(a), using Chapter 1, Lemma 4.10.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The E₈ used by the rank-one branch lies in the literal C_G(u)∩M.
Its existence is derived from the genuine global rank-two fusion theorem. -/
public theorem source16_elementary_eight_in_marked_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t u : G} (htM : t ∉ M) (hu : PFAppendixIII.IsInvolution u)
    (huD : u ∈ residualPairStabilizer M t) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      E ≤ centralizer ({u} : Set G) ∧ E ≤ M := by
  let : IsSimpleGroup G := r.simple
  obtain ⟨z,hz,hzM⟩ := h.nonempty
  have hnot : ¬ IsConj z u := by
    intro hc
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    have hzconj := h.invariant g z hz
    change MulAut.conj g z = u at hg
    rw [hg] at hzconj
    exact not_mem_Z_of_mem_residualPairStabilizer h htM huD hzconj
  obtain ⟨E,hEe,hEc,hEB⟩ := exists_elementary_eight_in_centralizer_of_simple
    (r.center_eq_bot h) z u
    (orderOf_eq_prime (h.involutions z hz).sq_eq_one (h.involutions z hz).ne_one)
    (orderOf_eq_prime hu.sq_eq_one hu.ne_one) hnot u
    (orderOf_eq_prime hu.sq_eq_one hu.ne_one)
  let B := centralizer ({u} : Set G)
  let S : Sylow 2 (B ⊓ M : Subgroup G) := default
  obtain ⟨_,z₁,_,_,_,T,hT⟩ := involutionCentralizer_sylow_and_marked_center h r hu huD.1 S
  let := hEe
  let EB := E.subgroupOf B
  have hp : IsPGroup 2 EB := (IsElementaryAbelian.isPGroup 2 E).of_equiv
    (subgroupOfEquivOfLe hEB).symm
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq B P T
  let f := B.subtype.comp (MulAut.conj b).toMonoidHom
  have hf : Function.Injective f := B.subtype_injective.comp (MulAut.conj b).injective
  have hmapT : EB.map f ≤ (T : Subgroup B).map B.subtype := by
    rintro x ⟨y,hy,rfl⟩
    refine ⟨MulAut.conj b y,?_,rfl⟩
    rw [← hb, Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨y,hP hy,rfl⟩
  refine ⟨EB.map f, ?_, ?_, hmapT.trans (map_subtype_le _), ?_⟩
  · let : IsElementaryAbelian 2 EB :=
      IsElementaryAbelian.subgroupOf hEB
    exact IsElementaryAbelian.map f
  · rw [card_map_of_injective hf, Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv]
    exact hEc
  · rw [hT] at hmapT
    exact hmapT.trans ((map_subtype_le _).trans inf_le_right)

/-- Lemma 16.3(a) on the original minimal-counterexample inputs, with the
rank-one and higher-rank branches both discharged. -/
public theorem source16_centralizer_nonsolvable
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t) :
    ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))) :=
  source16_centralizer_nonsolvable_of_rank_three_input h r ha ht htM hu huD
    (fun _ => source16_elementary_eight_in_marked_centralizer h.disconnected r htM hu huD)

/-- Lemma 16.3(c), with the earlier rank-two-centralizer theorem discharged. -/
public theorem source16_solvable_centralizer_le
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u v : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hv : PFAppendixIII.IsInvolution v) (hvM : v ∈ M)
    (hsol : Group.IsSolvable (localCircle Z (centralizer ({v} : Set G)))) :
    centralizer ({v} : Set G) ≤ M :=
  source16_solvable_centralizer_le_of_rank_three_input h r ha ht htM hu huD
    (fun _ => source16_elementary_eight_in_marked_centralizer h.disconnected r htM hu huD)
    hv hvM hsol

end BenderSuzuki.ZD
