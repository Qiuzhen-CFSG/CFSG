module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorus
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelection

/-!
# The selected torus fixed-space rank

Rank additivity along Z ≤ A ≤ V^i, with the literal action kernel Z,
gives rank(Z) + k + rank(Aut_A(V)) = rank(V). This uses the core actor
itself, before identifying it with a weak-closure offender normalizer.

For a Hermitian orbit of rank 9n and automizer two-rank at most 4n,
E.2.14(9)'s identification Z = C_V(x) therefore makes the torus fixed
space larger than 3n whenever k < 2n. This is the precise large-fixed-space
premise used by the proved parabolic exponent, on the original action.
The source fixed-space identity stays explicit; the endpoint k = 2n
and the full Hermitian exclusion are separate obligations.

Source: Aschbacher–Smith 8.2.2(7–8) and 8.2.3, printed pp.715–716,
using E.2.14(9), printed p.227 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem selected_core_actor_le_normalizer
    (s : Selected H T M V I k i S) :
    V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ≤
      normalizer (V : Set G) := by
  have hcoreM : (pCore 2 I).map I.subtype ≤ M := by
    rintro _ ⟨a,ha,rfl⟩
    apply (M.subgroupOf I).normalCore_le
    change a ∈ localCore M I
    rwa [s.core_eq]
  exact inf_le_right.trans ((le_inf hcoreM (map_subtype_le _)).trans
    (s.normalizer_eq ▸ inf_le_right))

/-- The rank identity for the selected core actor does not require its
prior identification with the whole offender normalizer. -/
theorem selected_actor_rank_identity (s : Selected H T M V I k i S) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    rank (V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) + k +
      rank (inducedAutomizer V A) = rank V := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let Z := V ⊓ W
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hAN : A ≤ normalizer (V : Set G) := selected_core_actor_le_normalizer s
  have hker : A ⊓ centralizer (V : Set G) = Z :=
    selected_actor_kernel I M V hVI S i s.twoConjugate
  have hr := rank_inducedAutomizer V A hAN
  rw [hker] at hr
  have hZA : Z ≤ A := hker ▸ inf_le_left
  have hc : subgroupCorank W A = k := by
    rw [conjugate_core_corank I V i.val i.property,
      ← quotient_rank_eq_core_corank I V hVI]
    exact s.rank_eq
  have hs := offender_corank_add hZA (show A ≤ W from inf_le_left)
  have hz := offender_corank_add (W := W) (A := Z) bot_le inf_le_right
  have hz' : rank W = subgroupCorank W Z + rank Z := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hz
  have hw : rank W = rank V := by
    dsimp only [W,rank]
    rw [card_map_of_injective (MulAut.conj i.val⁻¹).injective]
  change rank Z + k + rank (inducedAutomizer V A) = rank V
  omega

private theorem rank_automizerFixedGroup (X : Subgroup (Automizer V)) :
    rank (automizerFixedGroup V X) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) X) := by
  rw [rank,automizerFixedGroup,card_map_of_injective V.subtype_injective]
  change Nat.log 2 (Nat.card (fixedSpace (automizerRepresentation V) X)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)]

/-- The rank bounds on the actual automizer make the selected fixed
space larger than 3n throughout k < 2n. -/
theorem selected_fixed_rank_gt_three_mul
    (s : Selected H T M V I k i S) (n : ℕ)
    (hdim : rank V = 9*n) (hrank : primeRank 2 (Automizer V) ≤ 4*n)
    (hkn : k < 2*n) (x : Automizer V)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    3*n < Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := offender_elementary_of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_core_actor_le_normalizer s)
  have hb := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  have hi := selected_actor_rank_identity s
  change rank (V ⊓ W) + k + rank (inducedAutomizer V A) = rank V at hi
  have hf := rank_automizerFixedGroup (V := V) (zpowers x)
  rw [hfixed] at hf
  change rank (V ⊓ W) = _ at hf
  omega

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
