module

public import CFSG.Quasithin.Chapter16.Section04To05.Fusion
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The action and invariant subgroups in the Bender branch

The normalizer acts through its actual image in Aut(V). The kernel is the
relative centralizer, so the image is the source quotient N_G(V)/C_G(V).
Its action on an elementary abelian V is a faithful binary representation.
Tight embedding makes V ∩ K a TI-subgroup under the normalizer of V.
Faithfulness of R on L ensures that a conjugator carrying Ω₁(T_C) to Ω₁(R)
moves Ω₁(T_C).

The last lemma is the unitary obstruction: generators normalizing T_L
preserve its actual Frattini subgroup, which cannot be a nonzero proper
invariant subgroup of an irreducible V. The generation and irreducibility
premises must still be established in the source application.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1194–1195, Proposition 16.5.1. Left conjugation is used throughout.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G]

/-- The actual group of automorphisms induced by the ambient normalizer. -/
abbrev ActionImage (V : Subgroup G) := V.normalizerMonoidHom.range
/-- The canonical binary representation of the induced automorphism group. -/
noncomputable def normalizerRepresentation (V : Subgroup G) [IsElementaryAbelian 2 V] :
    Representation (ZMod 2) (ActionImage V) (Additive V) :=
  Representation.ofElementaryAbelianAction (p := 2)

/-- The image acts faithfully; no faithfulness certificate is assumed. -/
theorem normalizerRepresentation_faithful (V : Subgroup G) [IsElementaryAbelian 2 V] :
    Function.Injective (normalizerRepresentation V) := by
  intro a b h
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) h

/-- The action kernel is the centralizer inside the normalizer. -/
theorem normalizerAction_kernel (V : Subgroup G) :
    V.normalizerMonoidHom.ker =
      (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G)) :=
  V.normalizerMonoidHom_ker

/-- The first isomorphism theorem identifies the source quotient with the action image. -/
noncomputable def normalizerAction_quotient (V : Subgroup G) :
    (normalizer (V : Set G) ⧸ V.normalizerMonoidHom.ker) ≃* ActionImage V :=
  QuotientGroup.quotientKerEquivRange V.normalizerMonoidHom

/-- The source subgroup V = Ω₁(T_C) Ω₁(T_L), before elementary abelianness is proved. -/
def benderSpace (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  omegaOneAmbient (commutingSylow T L) ⊔ omegaOneAmbient (componentSylow T L)

/-- Both factors of V lie in the supplied Sylow subgroup. -/
theorem benderSpace_le_sylow (T : Sylow 2 G) (L : Subgroup G) :
    benderSpace T L ≤ (T : Subgroup G) :=
  sup_le ((omegaOneAmbient_le _).trans inf_le_left)
    ((omegaOneAmbient_le _).trans inf_le_left)

/-- First omega subgroups commute with an ambient automorphism. -/
theorem omega_map_equiv (H : Subgroup G) (e : G ≃* G) :
    omegaOneAmbient (H.map e.toMonoidHom) = (omegaOneAmbient H).map e.toMonoidHom := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro x ⟨y, hy, rfl⟩ hp
    have hy2 : y ^ 2 = 1 := by
      apply e.injective
      change e y ^ 2 = 1 at hp
      simpa only [map_pow, map_one] using hp
    exact mem_map_of_mem _ ((omegaOneAmbient_le_iff _ _).mp le_rfl y hy hy2)
  · rw [map_le_iff_le_comap]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro y hy hp
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl (e y) (mem_map_of_mem _ hy)
      (by simpa only [map_pow, map_one] using congrArg e hp)

/-- The equality R = T_C^g transports to their first omega subgroups. -/
theorem omega_conjugate {R C : Subgroup G} {g : G} (h : R = C.conjBy g) :
    omegaOneAmbient R = (omegaOneAmbient C).conjBy g := by
  rw [h]
  exact omega_map_equiv C (MulAut.conj g)

/-- The actual image of X ∩ N_G(V) in the normalizer action. -/
def inducedActor (V X : Subgroup G) : Subgroup (ActionImage V) :=
  (X.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom.rangeRestrict

/-- An ambient Sylow contained in N_G(V) maps onto a Sylow of the action image. -/
theorem sylow_inducedActor [Finite G] (V : Subgroup G) (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ∃ S : Sylow 2 (ActionImage V), (S : Subgroup (ActionImage V)) = inducedActor V T := by
  refine ⟨(T.subtype hT).mapSurjective V.normalizerMonoidHom.rangeRestrict_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  rfl

variable [Finite G]

/-- The supplied central involution belongs to Ω₁(T_C). -/
theorem commuting_omega_nontrivial {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) : omegaOneAmbient (commutingSylow T L) ≠ ⊥ := by
  have hzC : z ∈ commutingSylow T L := by
    refine ⟨h.mem_sylow, ?_⟩
    change z ∈ centralizer (L : Set G)
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  have hzU : z ∈ omegaOneAmbient (commutingSylow T L) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl z hzC ((orderOf_eq_prime_iff.mp h.involution).1)
  intro he
  have hz1 : z = 1 := mem_bot.mp (he ▸ hzU)
  simpa [hz1] using h.involution

/-- Faithfulness of R on L rules out stabilization of Ω₁(T_C). -/
theorem moving_commuting_omega {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : StandardSetup T z L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hconj : omegaOneAmbient R = (omegaOneAmbient (commutingSylow T L)).conjBy g) :
    g ∉ normalizer (omegaOneAmbient (commutingSylow T L) : Set G) := by
  intro hg
  have he : omegaOneAmbient R = omegaOneAmbient (commutingSylow T L) :=
    hconj.trans (mem_normalizer_iff_map_conj_eq.mp hg)
  apply commuting_omega_nontrivial h
  apply (omegaOneAmbient (commutingSylow T L)).eq_bot_iff_forall.mpr
  intro x hx
  exact disjoint_def.mp hfaith ((omegaOneAmbient_le R) (he.symm ▸ hx))
    (((omegaOneAmbient_le _).trans inf_le_right) hx)

/-- A two-subgroup intersected with a tightly embedded subgroup is TI under its normalizer. -/
theorem tight_intersection_TI {K V : Subgroup G}
    (hK : IsTightlyEmbedded K) (hV : IsPGroup 2 V) {g : G}
    (hg : g ∈ normalizer (V : Set G)) :
    (V ⊓ K).conjBy g = V ⊓ K ∨ Disjoint (V ⊓ K) ((V ⊓ K).conjBy g) := by
  by_cases hgK : g ∈ normalizer (K : Set G)
  · left
    change (V ⊓ K).map (MulAut.conj g).toMonoidHom = V ⊓ K
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    change V.conjBy g ⊓ K.conjBy g = V ⊓ K
    have hv : V.conjBy g = V := mem_normalizer_iff_map_conj_eq.mp hg
    have hk : K.conjBy g = K := mem_normalizer_iff_map_conj_eq.mp hgK
    rw [hv, hk]
  · right
    let Q := (V ⊓ K) ⊓ (V ⊓ K).conjBy g
    have hQ : IsPGroup 2 Q :=
      hV.of_injective (inclusion (inf_le_left.trans inf_le_left)) (inclusion_injective _)
    have hQK : Q ≤ K ⊓ K.conjBy g :=
      le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans (map_mono inf_le_right))
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    have hcop : (Nat.card Q).Coprime (Nat.card ↥(K ⊓ K.conjBy g)) := by
      rw [hn]
      exact (hK.2 g hgK).coprime_two_left.pow_left n
    have he := (disjoint_of_coprime_natCard hcop).eq_bot
    rw [inf_eq_left.mpr hQK] at he
    exact disjoint_iff.mpr he

omit [Finite G] in
/-- Normalizing P preserves the embedded Frattini subgroup of P. -/
theorem normalizer_le_frattini_normalizer (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer ((frattini P).map P.subtype : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let a := P.normalizerMonoidHom ⟨g, hg⟩
  have ha : a y ∈ frattini P :=
    frattini_le_comap_frattini_of_surjective (φ := a.toMonoidHom) a.surjective hy
  exact ⟨a y, ha, rfl⟩

omit [Finite G] in
/-- The actual Frattini subgroup obstructs an irreducible action generated by these conjugates. -/
theorem frattini_obstruction {P V X : Subgroup G} {g : G}
    (hX : X ≤ normalizer (P : Set G)) (hg : g ∈ normalizer (P : Set G))
    (hgen : normalizer (V : Set G) ≤ centralizer (V : Set G) ⊔ (X ⊔ X.conjBy g))
    (hPV : (frattini P).map P.subtype ≤ V)
    (hne : (frattini P).map P.subtype ≠ ⊥)
    (hproper : (frattini P).map P.subtype ≠ V)
    (hirr : ∀ W : Subgroup G, W ≤ V → normalizer (V : Set G) ≤ normalizer (W : Set G) →
      W = ⊥ ∨ W = V) : False := by
  have hXg : X.conjBy g ≤ normalizer (P : Set G) := by
    calc
      X.conjBy g ≤ (normalizer (P : Set G)).conjBy g := map_mono hX
      _ = normalizer (P : Set G) :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (P : Set G)).le_normalizer hg)
  have hN : normalizer (V : Set G) ≤ normalizer ((frattini P).map P.subtype : Set G) := by
    apply hgen.trans
    apply sup_le
    · exact (centralizer_le hPV).trans (centralizer_le_normalizer _)
    · exact (sup_le hX hXg).trans (normalizer_le_frattini_normalizer P)
  exact (hirr _ hPV hN).elim hne hproper
end CFSG.Quasithin.Chapter16.Intersections.Bender
