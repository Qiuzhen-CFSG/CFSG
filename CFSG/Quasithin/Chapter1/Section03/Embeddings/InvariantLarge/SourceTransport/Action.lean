module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge
public import Theory.Frattini.PGroupMap
public import Theory.Frattini.OmegaProducts

/-!
# Transport of the original complement and its normalizer action

An ambient homomorphism injective on P gives the actual image-complement
isomorphism and an equivariant isomorphism of Frattini quotients. Every
original element of N_T(P) maps into the image normalizer. Thus irreducibility
passes to that normalizer, while finite two-group Frattini functoriality
passes the identity P = [P, Φ(N_T(P))]. Cyclicity of the image automizer
pulls back through the same marked complement isomorphism.

This is the quotient transport used before A.3.15 in Aschbacher–Smith,
Proposition 1.3.4, printed pp.510–511. The image hypotheses are discharged
by the actual two-core and component-centralizer quotient in the source
ambient construction; no action or model conclusion is assumed here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SourceTransport
universe u v
variable {G : Type u} [Group G] {J : Type v} [Group J]
variable {p : ℕ} {T X P H M : Subgroup G}

structure PairAction (p : ℕ) (S B : Subgroup J) : Prop where
  oddComplement : XiOddQuotient p B
  irreducible : ∀ A : Subgroup (B ⧸ frattini B),
    (∀ s : (S ⊓ normalizer B : Subgroup J), ∀ a ∈ A,
      frattiniConjugationAction _ _ inf_le_right s a ∈ A) → A = ⊥ ∨ A = ⊤
  commutator : B = ⁅B, (frattini (S ⊓ normalizer B : Subgroup J)).map
    (S ⊓ normalizer B).subtype⁆

variable (f : M →* J) (hPM : P ≤ M) (hTM : T ≤ M)

abbrev imageComplement : Subgroup J := (P.subgroupOf M).map f
abbrev imageTwoGroup : Subgroup J := (T.subgroupOf M).map f

/-- Restrict the original ambient map to P. -/
def complementMap : P →* imageComplement (P := P) f :=
  (f.subgroupMap (P.subgroupOf M)).comp (subgroupOfEquivOfLe hPM).symm.toMonoidHom

def complementEquiv (hf : Function.Injective (f.comp (inclusion hPM))) :
    P ≃* imageComplement (P := P) f :=
  MulEquiv.ofBijective (complementMap f hPM) ⟨fun _ _ he => hf (congrArg Subtype.val he),
    (f.subgroupMap_surjective _).comp (subgroupOfEquivOfLe hPM).symm.surjective⟩

@[simp] theorem complementEquiv_coe (hf : Function.Injective (f.comp (inclusion hPM))) (x : P) :
    (complementEquiv f hPM hf x : J) = f (inclusion hPM x) := rfl

/-- The actual original normalizer maps into the actual image normalizer. -/
def normalizerMap : (T ⊓ normalizer P : Subgroup G) →*
    (imageTwoGroup (T := T) f ⊓ normalizer (imageComplement (P := P) f) : Subgroup J) :=
  (f.comp (inclusion (inf_le_left.trans hTM))).codRestrict _ (by
    intro s
    refine ⟨mem_map_of_mem f s.property.1, ?_⟩
    apply (P.subgroupOf M).le_normalizer_map
    refine ⟨inclusion (inf_le_left.trans hTM) s, ?_, rfl⟩
    change inclusion (inf_le_left.trans hTM) s ∈ normalizer (P.subgroupOf M : Set M)
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ P ↔ (s : G) * (x : G) * (s : G)⁻¹ ∈ P
    exact mem_normalizer_iff.mp s.property.2 x)

theorem complementEquiv_conjugation
    (hf : Function.Injective (f.comp (inclusion hPM)))
    (s : (T ⊓ normalizer P : Subgroup G)) (x : P) :
    complementEquiv f hPM hf (P.normalizerMonoidHom (inclusion inf_le_right s) x) =
      (imageComplement (P := P) f).normalizerMonoidHom
        (inclusion inf_le_right (normalizerMap f hTM s)) (complementEquiv f hPM hf x) := by
  apply Subtype.ext
  change f ((inclusion (inf_le_left.trans hTM) s) * (inclusion hPM x) *
      (inclusion (inf_le_left.trans hTM) s)⁻¹) =
    f (inclusion (inf_le_left.trans hTM) s) * f (inclusion hPM x) *
      (f (inclusion (inf_le_left.trans hTM) s))⁻¹
  rw [map_mul, map_mul, map_inv]

def frattiniEquiv (hf : Function.Injective (f.comp (inclusion hPM))) :
    (P ⧸ frattini P) ≃* (imageComplement (P := P) f ⧸ frattini (imageComplement (P := P) f)) :=
  QuotientGroup.congr _ _ (complementEquiv f hPM hf) (frattini_map_equiv _)

@[simp] theorem frattiniEquiv_mk
    (hf : Function.Injective (f.comp (inclusion hPM))) (x : P) :
    frattiniEquiv f hPM hf (QuotientGroup.mk' (frattini P) x) =
      QuotientGroup.mk' (frattini (imageComplement (P := P) f)) (complementEquiv f hPM hf x) := rfl

theorem frattiniEquiv_conjugation (hf : Function.Injective (f.comp (inclusion hPM)))
    (s : (T ⊓ normalizer P : Subgroup G)) (x : P ⧸ frattini P) :
    frattiniEquiv f hPM hf (frattiniConjugationAction _ _ inf_le_right s x) =
      frattiniConjugationAction _ _ inf_le_right (normalizerMap f hTM s)
        (frattiniEquiv f hPM hf x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    change frattiniEquiv f hPM hf
        (frattiniConjugationAction _ _ inf_le_right s (QuotientGroup.mk' (frattini P) x)) =
      frattiniConjugationAction _ _ inf_le_right (normalizerMap f hTM s)
        (frattiniEquiv f hPM hf (QuotientGroup.mk' (frattini P) x))
    simp only [frattiniConjugationAction, MonoidHom.comp_apply,
      frattiniEquiv_mk, quotientAut_apply_mk]
    congr 1
    exact complementEquiv_conjugation f hPM hTM hf s x

include hTM in
theorem image_irreducible (h : LocalInput p T X P H)
    (hf : Function.Injective (f.comp (inclusion hPM))) :
    ∀ A : Subgroup (imageComplement (P := P) f ⧸ frattini (imageComplement (P := P) f)),
      (∀ s : (imageTwoGroup (T := T) f ⊓ normalizer (imageComplement (P := P) f) : Subgroup J), ∀ a ∈ A,
        frattiniConjugationAction _ _ inf_le_right s a ∈ A) → A = ⊥ ∨ A = ⊤ := by
  intro A hA
  let e := frattiniEquiv f hPM hf
  have he : ∀ s : (T ⊓ normalizer P : Subgroup G), ∀ a ∈ A.comap e.toMonoidHom,
      frattiniConjugationAction _ _ inf_le_right s a ∈ A.comap e.toMonoidHom := by
    intro s a ha
    change e (frattiniConjugationAction _ _ inf_le_right s a) ∈ A
    rw [frattiniEquiv_conjugation f hPM hTM hf]
    exact hA _ _ ha
  have hi := h.irreducible (A.comap e.toMonoidHom) he
  rcases hi with hi | hi
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) hi
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) hi
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm

include hPM hTM in
theorem image_frattini_commutator [Finite G] [Finite J] (h : LocalInput p T X P H) :
    imageComplement (P := P) f =
      ⁅imageComplement (P := P) f,
        (frattini (imageTwoGroup (T := T) f ⊓ normalizer (imageComplement (P := P) f) : Subgroup J)).map
          (imageTwoGroup (T := T) f ⊓ normalizer (imageComplement (P := P) f)).subtype⁆ := by
  let N := T ⊓ normalizer P
  let A := (frattini N).map N.subtype
  have hNM : N ≤ M := inf_le_left.trans hTM
  have hAM : A ≤ M := (map_subtype_le _).trans hNM
  have he : A.subgroupOf M = (frattini N).map (inclusion hNM) := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hAM, map_map]
    rfl
  have hi : P.subgroupOf M = ⁅P.subgroupOf M, A.subgroupOf M⁆ := by
    apply map_injective M.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hPM, map_subgroupOf_eq_of_le hAM]
    exact h.frattini_commutator
  have hh := congrArg (map f) hi
  rw [map_commutator, he, map_map] at hh
  let V := imageTwoGroup (T := T) f ⊓ normalizer (imageComplement (P := P) f)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 N) := ⟨h.two_group.to_le inf_le_left⟩
  let : Fact (IsPGroup 2 V) :=
    ⟨(h.two_group.comap_subtype.map f).to_le inf_le_left⟩
  have hj := map_mono (f := V.subtype)
    (frattini_map_le_of_isPGroup (p := 2) (normalizerMap (P := P) f hTM))
  rw [map_map] at hj
  apply le_antisymm
  · exact hh.le.trans (commutator_mono le_rfl hj)
  · rw [commutator_comm]
    apply le_normalizer_iff_commutator_le_right.mp
    exact (map_subtype_le _).trans inf_le_right

include hTM in
theorem image_pairAction [Finite G] [Finite J] (h : LocalInput p T X P H)
    (hf : Function.Injective (f.comp (inclusion hPM))) :
    PairAction p (imageTwoGroup (T := T) f) (imageComplement (P := P) f) :=
  ⟨h.odd_complement.of_mulEquiv (complementEquiv f hPM hf),
    image_irreducible f hPM hTM h hf, image_frattini_commutator f hPM hTM h⟩

include hTM in
theorem automizer_cyclic_of_image
    (hf : Function.Injective (f.comp (inclusion hPM)))
    (hc : IsCyclic (automizer (imageTwoGroup (T := T) f) (imageComplement (P := P) f))) :
    IsCyclic (automizer T P) := by
  let _ := hc
  let e := MulAut.congr (complementEquiv f hPM hf)
  let j : automizer T P →*
      automizer (imageTwoGroup (T := T) f) (imageComplement (P := P) f) :=
    (e.toMonoidHom.comp (automizer T P).subtype).codRestrict _ (by
      intro a
      obtain ⟨s, hs⟩ := a.property
      refine ⟨normalizerMap f hTM s, ?_⟩
      change _ = e a.val
      rw [← hs]
      apply MulEquiv.ext
      intro b
      obtain ⟨x, rfl⟩ := (complementEquiv f hPM hf).surjective b
      simpa only [e, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MonoidHom.comp_apply]
        using (complementEquiv_conjugation f hPM hTM hf s x).symm)
  exact isCyclic_of_injective j (fun a b hab =>
    Subtype.ext (e.injective (congrArg Subtype.val hab)))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SourceTransport
