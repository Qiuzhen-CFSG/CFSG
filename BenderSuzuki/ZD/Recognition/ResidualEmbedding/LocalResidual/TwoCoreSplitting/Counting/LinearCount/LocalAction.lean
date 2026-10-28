module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.Algebra
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# The marked local action in Section 17

The ambient distinguished centralizer closure is canonically isomorphic to
its internal version. Conjugation transports this actual closure, and hence
its model, while retaining the original marked involutions. The twisted
involution interchanges the original two cosets. Consequently the fixed-set
assertion of Lemma 17.2(e) says that its local odd subgroup fixes no point
fixed by that involution.

Source: GLS4, Chapter 2, (17B), Lemmas 17.2 and 17.4.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17
open Subgroup PFAppendixIII Theory.GroupTheory
variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}

/-- The internal and ambient distinguished closures have the same carrier,
through the actual centralizer subtype map. -/
public def internalCentralizerClosureEquiv (Z : Set G) (u : G) :
    closure ((centralizer ({u} : Set G)).subtype ⁻¹' Z) ≃*
      centralizerClosure Z u :=
  ((closure ((centralizer ({u} : Set G)).subtype ⁻¹' Z)).equivMapOfInjective
    (centralizer ({u} : Set G)).subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (centralizerClosure_eq_map Z u).symm)

private theorem conj_mem (h : IsProductDisconnected Z M) (g u : G) {x : G}
    (hx : x ∈ centralizerClosure Z u) :
    MulAut.conj g x ∈ centralizerClosure Z (MulAut.conj g u) := by
  have hle : centralizerClosure Z u ≤
      (centralizerClosure Z (MulAut.conj g u)).comap (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    intro z hz
    exact mem_centralizerClosure (h.invariant g z hz.1)
      ((show Commute z u from mem_centralizer_singleton_iff.mp hz.2).map
        (MulAut.conj g).toMonoidHom)
  exact hle hx

/-- Fusion of the marked elements gives an actual equivalence of their
circles; an abstract isomorphism of models is not used to infer fusion. -/
public theorem centralizerClosure_equiv_of_isConj
    (h : IsProductDisconnected Z M) {u v : G} (huv : IsConj u v) :
    Nonempty (centralizerClosure Z u ≃* centralizerClosure Z v) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp huv
  have he : (centralizerClosure Z u).map (MulAut.conj g).toMonoidHom =
      centralizerClosure Z (MulAut.conj g u) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact conj_mem h g u hx
    · intro x hx
      refine ⟨MulAut.conj g⁻¹ x, ?_, ?_⟩
      · have hh := conj_mem h g⁻¹ (MulAut.conj g u) hx
        have hg : MulAut.conj g⁻¹ (MulAut.conj g u) = u := by
          simp only [MulAut.conj_apply, inv_inv]
          group
        rwa [hg] at hh
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
  exact ⟨((centralizerClosure Z u).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr he)⟩


/-- The element t of the original configuration belongs to C_G(tu)°. -/
public theorem t_mem_twisted_circle (d : TwoCoreLocalData Z M) :
    d.t ∈ centralizerClosure Z (d.t * ((d.u : M) : G)) :=
  mem_centralizerClosure d.t_mem ((Commute.refl d.t).mul_right d.commutes_t.symm)

/-- The original pair subgroup, moved into the literal local circle. -/
public def twistedPairEquiv (d : TwoCoreLocalData Z M) :
    (residualPairStabilizer M d.t ⊓
      centralizerClosure Z (d.t * ((d.u : M) : G))).subgroupOf
        (centralizerClosure Z (d.t * ((d.u : M) : G))) ≃*
    (residualPairStabilizer M d.t ⊓
      centralizerClosure Z (d.t * ((d.u : M) : G)) : Subgroup G) :=
  subgroupOfEquivOfLe inf_le_right

/-- Lemma 17.2(c,d) in the precise carrier needed by the torus theorems.
The normalizer bound in 17.2(f) is not part of this assertion. -/
public theorem twistedPair_intrinsic (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) :
    let L := centralizerClosure Z (d.t * ((d.u : M) : G))
    let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
    let t : L := ⟨d.t, t_mem_twisted_circle d⟩
    Odd (Nat.card H) ∧ orderOf t = 2 ∧
      t ∈ normalizer (H : Set L) ∧
      (centralizer ({t} : Set L)).relIndex H ≠ 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (twistedPairEquiv d).toEquiv]
    exact d.odd_twisted_pair
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (h.involutions d.t d.t_mem).sq_eq_one
      (h.involutions d.t d.t_mem).ne_one
  · rw [mem_normalizer_iff]
    intro x
    exact mem_normalizer_iff.mp d.normalizes_twisted_pair x.val
  · intro he
    apply d.noncentral_twisted_pair
    have hc := relIndex_eq_one.mp he
    intro x hx
    have hh : (⟨x, hx.2⟩ : centralizerClosure Z (d.t * ((d.u : M) : G))) ∈
        (residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G))).subgroupOf
            (centralizerClosure Z (d.t * ((d.u : M) : G))) := hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hc hh)))

/-- The local torus index is the relative centralizer index in the
original ambient group. This keeps the two subgroup-of conventions aligned. -/
public theorem twistedPair_index_eq_ambient (d : TwoCoreLocalData Z M) :
    let L := centralizerClosure Z (d.t * ((d.u : M) : G))
    let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
    let t : L := ⟨d.t, t_mem_twisted_circle d⟩
    (centralizer ({t} : Set L)).relIndex H =
      (centralizer ({d.t} : Set G)).relIndex (residualPairStabilizer M d.t ⊓ L) := by
  let L := centralizerClosure Z (d.t * ((d.u : M) : G))
  let t : L := ⟨d.t, t_mem_twisted_circle d⟩
  have he : centralizer ({t} : Set L) = (centralizer ({d.t} : Set G)).comap L.subtype := by
    ext x
    simp only [mem_centralizer_singleton_iff, mem_comap]
    exact Subtype.ext_iff
  change (centralizer ({t} : Set L)).relIndex _ = _
  rw [he, relIndex_comap, map_subgroupOf_eq_of_le inf_le_right]

/-- The actual product tu interchanges the two original points. -/
public theorem twisted_involution_swaps (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) :
    let a : G ⧸ M := QuotientGroup.mk 1
    let b := d.t • a
    (d.t * ((d.u : M) : G)) • a = b ∧
      (d.t * ((d.u : M) : G)) • b = a ∧ a ≠ b := by
  let a : G ⧸ M := QuotientGroup.mk 1
  have hu : (((d.u : M) : G)) • a = a := by
    change ((d.u : M) : G) ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rw [MulAction.stabilizer_quotient]
    exact (d.u : M).property
  have htt : d.t * d.t = 1 := by
    simpa only [pow_two] using (h.involutions d.t d.t_mem).sq_eq_one
  refine ⟨?_, ?_, ?_⟩
  · change (d.t * ((d.u : M) : G)) • a = d.t • a
    rw [mul_smul, hu]
  · change (d.t * ((d.u : M) : G)) • (d.t • a) = a
    rw [← mul_smul, mul_assoc, d.commutes_t.eq, ← mul_assoc, htt, one_mul, hu]
  · intro he
    apply d.t_not_mem
    have ht : d.t ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) := he.symm
    simpa only [MulAction.stabilizer_quotient] using ht

/-- The exact fixed-set clause 17.2(e) excludes fixed points of D₀ inside
Ω_tu. In particular this conclusion uses the original coset action. -/
public theorem twistedPair_no_common_fixed_point
    (h : IsProductDisconnected Z M) (d : TwoCoreLocalData Z M)
    (hfix : ∀ gamma : G ⧸ M,
      residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma ↔
      gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M)) :
    ∀ gamma : G ⧸ M, (d.t * ((d.u : M) : G)) • gamma = gamma →
      ¬ residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma := by
  intro gamma hgamma hD
  obtain ⟨hab, hba, hne⟩ := twisted_involution_swaps h d
  rcases (hfix gamma).mp hD with rfl | rfl
  · exact hne (hgamma.symm.trans hab)
  · exact hne (hba.symm.trans hgamma)

variable [Finite G]

private theorem sylow_normalizer_fixes_coset
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : (Z ∩ (Q : Set G)).Nonempty) :
    ∃ gamma : G ⧸ M, normalizer (Q : Set G) ≤ MulAction.stabilizer G gamma := by
  obtain ⟨S, hSM, _⟩ := r.fusion
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hQM : Q.map (MulAut.conj g).toMonoidHom ≤ M := by
    apply le_trans (map_mono hQT)
    have he : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) :=
      congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
    rwa [he]
  obtain ⟨z, hzZ, hzQ⟩ := hne
  have hn := normalizer_le h hQM
    ⟨MulAut.conj g z, h.invariant g z hzZ, mem_map_of_mem _ hzQ⟩
  refine ⟨g⁻¹ • (QuotientGroup.mk 1 : G ⧸ M), ?_⟩
  intro x hx
  have hxm : MulAut.conj g x ∈ M :=
    hn (le_normalizer_map _ (mem_map_of_mem _ hx))
  have hxfix : MulAut.conj g x • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    change MulAut.conj g x ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    simpa only [MulAction.stabilizer_quotient] using hxm
  change x • (g⁻¹ • (QuotientGroup.mk 1 : G ⧸ M)) = g⁻¹ • (QuotientGroup.mk 1 : G ⧸ M)
  calc
    _ = g⁻¹ • (MulAut.conj g x • (QuotientGroup.mk 1 : G ⧸ M)) := by
      simp only [MulAut.conj_apply, mul_smul, inv_smul_smul]
    _ = _ := congrArg (fun a : G ⧸ M => g⁻¹ • a) hxfix

/-- The genuine local action excludes D₀ from every Sylow two-normalizer
of C_G(tu)°. This supplies the group-theoretic part of the unitary no-Borel
condition, without assuming a permutation-model identification. -/
public theorem twistedPair_not_le_sylow_normalizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (d : TwoCoreLocalData Z M)
    (hfix : ∀ gamma : G ⧸ M,
      residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma ↔
      gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M)) :
    let L := centralizerClosure Z (d.t * ((d.u : M) : G))
    let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
    ∀ S : Sylow 2 L, ¬ H ≤ normalizer (S : Set L) := by
  dsimp only
  let L := centralizerClosure Z (d.t * ((d.u : M) : G))
  let t : L := ⟨d.t, t_mem_twisted_circle d⟩
  intro S hS
  let Q : Subgroup G := (S : Subgroup L).map L.subtype
  have ht : orderOf t = 2 ^ 1 := by
    simpa only [pow_one] using (twistedPair_intrinsic h d).2.1
  obtain ⟨s, hs⟩ := S.exists_isConj_of_orderOf_eq_prime_pow ht
  have hsZ : ((s : L) : G) ∈ Z := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hs
    have he : MulAut.conj (g : G) d.t = ((s : L) : G) := congrArg Subtype.val hg
    rw [← he]
    exact h.invariant (g : G) d.t d.t_mem
  obtain ⟨gamma, hgamma⟩ := sylow_normalizer_fixes_coset h r Q
    (S.isPGroup'.map L.subtype) ⟨((s : L) : G), hsZ, mem_map_of_mem _ s.property⟩
  have hw : d.t * ((d.u : M) : G) ∈ normalizer (Q : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rintro x ⟨y, _, rfl⟩
    exact mem_centralizer_singleton_iff.mp (centralizerClosure_le Z _ y.property)
  have hD : residualPairStabilizer M d.t ⊓ L ≤ MulAction.stabilizer G gamma := by
    intro x hx
    apply hgamma
    have hn : (⟨x, hx.2⟩ : L) ∈ normalizer (S : Set L) := hS hx
    exact le_normalizer_map L.subtype (mem_map_of_mem _ hn)
  exact twistedPair_no_common_fixed_point h d hfix gamma (hgamma hw) hD

end BenderSuzuki.ZD.Section17
