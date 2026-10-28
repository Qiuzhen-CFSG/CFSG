module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Source
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.Quotient
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization

/-!
# The linear seed in the original terminal component argument

A normal subgroup K with K/O₂(K) isomorphic to PSL₃(4), together with
H = KT and minimal parabolicity over T, has a Sylow element exchanging the
two parabolic conjugacy classes. Quotient H by the embedded O₂(K), use the
linear-three source theorem on the actual image of K, and lift both
parabolic equations through this quotient. The kernel belongs to each
lifted parabolic, so equality of quotient images gives equality upstairs.

The final theorem applies this construction to K = O²(H) for an original
H-star member. It retains the inclusion into the containing centralizer
and the literal residual equality from 5.2.3; no diagram-action hypothesis
is added to that earlier theorem.

Source: Aschbacher--Smith, E.2.2(2b), printed pp.215--216, and the linear
branch of 13.6.27, printed p.934 (PDF p.951).
-/

public section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.MinimalParabolicWitness
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
variable {H : Type*} [Group H] [Finite H]
private instance core_normal (K : Subgroup H) [K.Normal] : (K.pCoreIn 2).Normal :=
  inferInstanceAs (((pCore 2 K).map K.subtype).Normal)

private noncomputable def coreQuotientEquiv (K : Subgroup H) [K.Normal] :
    (K ⧸ pCore 2 K) ≃* K.map (QuotientGroup.mk' (K.pCoreIn 2)) := by
  let q := QuotientGroup.mk' (K.pCoreIn 2)
  have he : (q.subgroupMap K).ker = pCore 2 K := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective K.subtype_injective _
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
      (q.subgroupMap_surjective K))

omit [Finite H] in
private theorem coreQuotientEquiv_mk (K : Subgroup H) [K.Normal] (k : K) :
    coreQuotientEquiv K (QuotientGroup.mk' (pCore 2 K) k) =
      (QuotientGroup.mk' (K.pCoreIn 2)).subgroupMap K k := by
  rfl

omit [Finite H] in
private theorem map_liftedParabolic (K : Subgroup H) [K.Normal]
    (e : (K ⧸ pCore 2 K) ≃* L3Four) (P : Subgroup L3Four) :
    (liftedParabolic K e P).map (QuotientGroup.mk' (K.pCoreIn 2)) =
      P.map (modelEmbedding F4 (K.map (QuotientGroup.mk' (K.pCoreIn 2)))
        ((coreQuotientEquiv K).symm.trans e)) := by
  let q := QuotientGroup.mk' (K.pCoreIn 2)
  let E := (coreQuotientEquiv K).symm.trans e
  ext x
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨e (QuotientGroup.mk' (pCore 2 K) k),hk,?_⟩
    change ((coreQuotientEquiv K) (e.symm (e (QuotientGroup.mk' (pCore 2 K) k))) :
      H ⧸ K.pCoreIn 2) = _
    simp only [e.symm_apply_apply, coreQuotientEquiv_mk]
    rfl
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (e.symm y)
    refine ⟨k, ⟨k,?_,rfl⟩, ?_⟩
    · change e (QuotientGroup.mk' (pCore 2 K) k) ∈ P
      rw [hk,e.apply_symm_apply]
      exact hy
    · change q k = ((coreQuotientEquiv K) (e.symm y) : H ⧸ K.pCoreIn 2)
      rw [← hk, coreQuotientEquiv_mk]
      rfl

omit [Finite H] in
private theorem core_le_liftedParabolic (K : Subgroup H)
    (e : (K ⧸ pCore 2 K) ≃* L3Four) (P : Subgroup L3Four) :
    K.pCoreIn 2 ≤ liftedParabolic K e P := by
  apply map_mono
  intro k hk
  change e (QuotientGroup.mk' (pCore 2 K) k) ∈ P
  have he : QuotientGroup.mk' (pCore 2 K) k = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hk
  rw [he, map_one]
  exact P.one_mem

omit [Finite H] in
private theorem map_conj_hom {X : Type*} [Group X] (f : H →* X)
    (P : Subgroup H) (h : H) :
    (P.map (MulAut.conj h).toMonoidHom).map f =
      (P.map f).map (MulAut.conj (f h)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
    map_mul, map_inv]

omit [Finite H] in
private theorem core_le_conjugate (K : Subgroup H) [K.Normal]
    (e : (K ⧸ pCore 2 K) ≃* L3Four) (P : Subgroup L3Four) (h : H) :
    K.pCoreIn 2 ≤ (liftedParabolic K e P).map (MulAut.conj h).toMonoidHom := by
  have hn : h ∈ normalizer (K.pCoreIn 2 : Set H) := by rw [normalizer_eq_top]; trivial
  exact (mem_normalizer_iff_map_conj_eq.mp hn) ▸ map_mono (core_le_liftedParabolic K e P)

private theorem f4_card : Nat.card F4 = 2 ^ 2 := by
  exact GaloisField.card 2 2 (by decide)


/-- Minimal parabolicity forces a genuine exchange of the two linear-three
parabolic classes on the original normal subgroup, before quotienting. -/
theorem exists_nontrivialDynkinAction_of_minimalParabolic
    (K : Subgroup H) [K.Normal] (e : (K ⧸ pCore 2 K) ≃* L3Four)
    (T : Sylow 2 H) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) :
    ∃ e' : (K ⧸ pCore 2 K) ≃* L3Four, NontrivialDynkinAction (T : Subgroup H) K e' := by
  let q := QuotientGroup.mk' (K.pCoreIn 2)
  let D := K.map q
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (K.pCoreIn 2))
  have hgen' : D ⊔ (S : Subgroup (H ⧸ K.pCoreIn 2)) = ⊤ := by
    change K.map q ⊔ (T : Subgroup H).map q = ⊤
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hP' : ChapterB.IsMinimalParabolicOver S ⊤ :=
    ChapterB.minimalParabolic_surjective T hP q (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact (isPGroup_pCoreIn 2 K).le_sylow_of_normal T)
  obtain ⟨g,_,⟨t,ht,ha⟩,_⟩ := ChapterE.Structure.LinearThree.exists_diagram_and_borel
    F4 (by decide : 0 < 2) f4_card D ((coreQuotientEquiv K).symm.trans e) S hgen' hP'
  let e' := e.trans (MulAut.conj g)
  let E := (coreQuotientEquiv K).symm.trans e'
  change diagramAction F4 (by decide : 0 < 2) f4_card (modelAction F4 D E t) ≠ 1 at ha
  obtain ⟨u,hu,rfl⟩ := ht
  have hswap (b : Bool) :
      diagramAction F4 (by decide : 0 < 2) f4_card (modelAction F4 D E (q u)) b = !b := by
    let a := diagramAction F4 (by decide : 0 < 2) f4_card (modelAction F4 D E (q u))
    have hinj := a.injective
    cases hp : a false <;> cases hq : a true
    · exact (Bool.false_ne_true (hinj (hp.trans hq.symm))).elim
    · have he : a = 1 := by ext b; cases b <;> assumption
      exact (ha he).elim
    · cases b <;> assumption
    · exact (Bool.false_ne_true (hinj (hp.trans hq.symm))).elim
  have hclass (b : Bool) : ∃ k : K,
      (liftedParabolic K e' (parabolic F4 b)).map (MulAut.conj u).toMonoidHom =
        (liftedParabolic K e' (parabolic F4 (!b))).map
          (MulAut.conj (k : H)).toMonoidHom := by
    obtain ⟨a,ha'⟩ := diagramAction_spec F4 (by decide : 0 < 2) f4_card
      (modelAction F4 D E (q u)) b
    rw [hswap] at ha'
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (e'.symm a)
    have hk' : q k = modelEmbedding F4 D E a := by
      change q k = ((coreQuotientEquiv K) (e'.symm a) : H ⧸ K.pCoreIn 2)
      rw [← hk, coreQuotientEquiv_mk]
      rfl
    refine ⟨k, ?_⟩
    apply map_injective_of_ker_le q
      (by rw [QuotientGroup.ker_mk']; exact core_le_conjugate K e' _ u)
      (by rw [QuotientGroup.ker_mk']; exact core_le_conjugate K e' _ k)
    rw [map_conj_hom, map_conj_hom, map_liftedParabolic, map_liftedParabolic]
    change ((parabolic F4 b).map (modelEmbedding F4 D E)).map
        (MulAut.conj (q u)).toMonoidHom = _
    rw [← map_modelAction, ha', map_conj_hom, hk']
  obtain ⟨k₀,hk₀⟩ := hclass true
  obtain ⟨k₁,hk₁⟩ := hclass false
  exact ⟨e', le_normalizer_of_normal, u, hu, k₀, k₁, hk₀, hk₁⟩

section Transport
variable {X : Type*} [Group X]
variable (f : H →* X) (hf : Function.Injective f) (K : Subgroup H)

private noncomputable def mappedMark (e : (K ⧸ pCore 2 K) ≃* L3Four) :
    (K.map f ⧸ pCore 2 (K.map f)) ≃* L3Four :=
  (QuotientGroup.congr _ _ (K.equivMapOfInjective f hf)
    (pCore_map_iso 2 (K.equivMapOfInjective f hf))).symm.trans e

omit [Finite H] in
private theorem mappedMark_mk (e : (K ⧸ pCore 2 K) ≃* L3Four) (k : K) :
    mappedMark f hf K e
      (QuotientGroup.mk' (pCore 2 (K.map f)) (K.equivMapOfInjective f hf k)) =
      e (QuotientGroup.mk' (pCore 2 K) k) := by
  let c := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map f))
    (K.equivMapOfInjective f hf) (pCore_map_iso 2 (K.equivMapOfInjective f hf))
  change e (c.symm (c (QuotientGroup.mk' (pCore 2 K) k))) = _
  rw [c.symm_apply_apply]

omit [Finite H] in
private theorem liftedParabolic_map_injective (e : (K ⧸ pCore 2 K) ≃* L3Four)
    (P : Subgroup L3Four) :
    (liftedParabolic K e P).map f = liftedParabolic (K.map f) (mappedMark f hf K e) P := by
  ext x
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨K.equivMapOfInjective f hf k,?_,rfl⟩
    change mappedMark f hf K e
      (QuotientGroup.mk' (pCore 2 (K.map f)) (K.equivMapOfInjective f hf k)) ∈ P
    rw [mappedMark_mk]
    exact hk
  · rintro ⟨d,hd,rfl⟩
    obtain ⟨k,rfl⟩ := (K.equivMapOfInjective f hf).surjective d
    refine ⟨k,⟨k,?_,rfl⟩,rfl⟩
    change mappedMark f hf K e
      (QuotientGroup.mk' (pCore 2 (K.map f)) (K.equivMapOfInjective f hf k)) ∈ P at hd
    rwa [mappedMark_mk] at hd

omit [Finite H] in
include hf in
/-- The literal parabolic equations are preserved under an injective embedding. -/
theorem nontrivialDynkinAction_map (T : Subgroup H)
    (e : (K ⧸ pCore 2 K) ≃* L3Four) (hd : NontrivialDynkinAction T K e) :
    ∃ e' : (K.map f ⧸ pCore 2 (K.map f)) ≃* L3Four,
      NontrivialDynkinAction (T.map f) (K.map f) e' := by
  obtain ⟨hn,t,ht,k₀,k₁,h₀,h₁⟩ := hd
  refine ⟨mappedMark f hf K e, (map_mono hn).trans (K.le_normalizer_map f),
    f t,mem_map_of_mem f ht,K.equivMapOfInjective f hf k₀,
    K.equivMapOfInjective f hf k₁,?_,?_⟩
  · have hh := congrArg (Subgroup.map f) h₀
    simpa only [map_conj_hom, liftedParabolic_map_injective f hf,
      coe_equivMapOfInjective_apply] using hh
  · have hh := congrArg (Subgroup.map f) h₁
    simpa only [map_conj_hom, liftedParabolic_map_injective f hf,
      coe_equivMapOfInjective_apply] using hh
end Transport

variable {G : Type*} [Group G] [Finite G]

/-- The original H-star residual in any containing local group has the diagram
actor forced by its actual Sylow and minimal-parabolic geometry. -/
theorem residual_diagram_of_HStar_in_overgroup
    (T : Sylow 2 G) {M A C : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hA : A ∈ Chapter3.HStar (T : Subgroup G) M)
    (hNT : normalizer (T : Set G) ≤ M) (hAC : A ≤ C)
    (e : (pResidual 2 A ⧸ pCore 2 (pResidual 2 A)) ≃* L3Four) :
    ∃ e' : ((pResidual 2 A).map (inclusion hAC) ⧸
        pCore 2 ((pResidual 2 A).map (inclusion hAC))) ≃* L3Four,
      NontrivialDynkinAction ((T : Subgroup G).subgroupOf C)
        ((pResidual 2 A).map (inclusion hAC)) e' := by
  have hTA : (T : Subgroup G) ≤ A := hA.1.1.2
  let S := T.subtype hTA
  have hP : ChapterB.IsMinimalParabolicOver S ⊤ :=
    ChapterE.Section06.FixedPointBounds.ParabolicCartan.minimalParabolic_subtype T A
      (Chapter3.HStar.minimalParabolic T hTM hA (Or.inl hNT))
  obtain ⟨e',hd⟩ := exists_nontrivialDynkinAction_of_minimalParabolic
    (pResidual 2 A) e S (pResidual_sup_sylow_eq_top S) hP
  obtain ⟨e'',hd'⟩ := nontrivialDynkinAction_map
    (inclusion hAC) (inclusion_injective hAC) (pResidual 2 A) (S : Subgroup A) e' hd
  have hS : (S : Subgroup A).map (inclusion hAC) = (T : Subgroup G).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (hTA.trans hAC)]
    change ((T : Subgroup G).subgroupOf A).map A.subtype = _
    exact map_subgroupOf_eq_of_le hTA
  exact ⟨e'',hS ▸ hd'⟩

/-- The linear equality in source 5.2.3 supplies the exact 13.6.27 candidate;
the nontrivial diagram action is proved, not added to that equality. -/
theorem linear_candidate_of_HStar
    (T : Sylow 2 G) {M A C : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hA : A ∈ Chapter3.HStar (T : Subgroup G) M)
    (hNT : normalizer (T : Set G) ≤ M) (hAC : A ≤ C)
    (e : (pResidual 2 A ⧸ pCore 2 (pResidual 2 A)) ≃* L3Four)
    (K : Subgroup C)
    (hK : (pResidual 2 A).map A.subtype = K.map C.subtype) :
    Candidate ((T : Subgroup G).subgroupOf C) K := by
  have he : (pResidual 2 A).map (inclusion hAC) = K := by
    apply map_injective C.subtype_injective
    rw [map_map]
    exact hK
  have hd := residual_diagram_of_HStar_in_overgroup T hTM hA hNT hAC e
  rw [he] at hd
  exact Or.inr (Or.inr hd)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
