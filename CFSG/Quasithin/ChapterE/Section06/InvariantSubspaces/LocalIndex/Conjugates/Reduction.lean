module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Calculations
public import Theory.Frattini.CentralElementarySupplement
public import Theory.ElementaryAbelian.Join

/-!
# Elementary deductions from the conjugate-block factorizations

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
C.5.6(4),(5), printed pp.157–158, and C.5.7, printed p.160.

Given `Q = UD`, `D ≤ C_S(Uˣ)` and `S = UˣQ`, both `Q` and `Qˣ` have
central elementary supplements over their intersection. Thus their embedded
Frattini subgroups coincide, and `Φ(Q) = Φ(D)` gives the required invariance.
The family argument transports maximum order and relative normality under
conjugation, then identifies the second candidate with the conjugate core.

The actual block-extension and maximum-family calculations remain explicit
premises. The elementary candidates established here do not assert maximality.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates

open Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G} {x : G}

private theorem map_centralizer_equiv (E : Subgroup G) (e : G ≃* G) :
    (centralizer (E : Set G)).map e.toMonoidHom =
      centralizer (E.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e y) (mem_map_of_mem _ hy)

private theorem map_frattini_equiv (B : Subgroup G) (e : G ≃* G) :
    ((frattini B).map B.subtype).map e.toMonoidHom =
      (frattini (B.map e.toMonoidHom)).map (B.map e.toMonoidHom).subtype := by
  let f := e.subgroupMap B
  have hf : (frattini B).map f.toMonoidHom = frattini (B.map e.toMonoidHom) :=
    f.mapSubgroup.map_radical
  apply le_antisymm
  · rintro g ⟨b, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨f d, hf ▸ mem_map_of_mem f.toMonoidHom hd, ?_⟩
    exact MulEquiv.coe_subgroupMap_apply e B d
  · rintro g ⟨b, hb, rfl⟩
    have hb' : b ∈ (frattini B).map f.toMonoidHom := hf.symm ▸ hb
    obtain ⟨d, hd, hdb⟩ := hb'
    refine ⟨(d : G), mem_map_of_mem B.subtype hd, ?_⟩
    exact (MulEquiv.coe_subgroupMap_apply e B d).symm.trans
      (congrArg Subtype.val hdb)

private theorem supplement_intersection (P V W : Subgroup G)
    (hVP : V ≤ P) (hspan : P ≤ V ⊔ W) (hVW : V ≤ normalizer (W : Set G)) :
    P = V ⊔ (P ⊓ W) := by
  apply le_antisymm
  · intro g hg
    have hgm : g ∈ (V : Set G) * (W : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right V W hVW]
      exact hspan hg
    obtain ⟨v, hv, w, hw, hvg⟩ := hgm
    have hwP : w ∈ P := by
      have hh := P.mul_mem (P.inv_mem (hVP hv)) hg
      rwa [← hvg, inv_mul_cancel_left] at hh
    rw [← hvg]
    exact (V ⊔ (P ⊓ W)).mul_mem (mem_sup_left hv) (mem_sup_right ⟨hwP, hw⟩)
  · exact sup_le hVP inf_le_left

/-- The core is normal in the Baumann subgroup, as it is the two-core of `LS`. -/
theorem S_normalizes_Q (R L : Subgroup G) : S R ≤ normalizer (Q R L : Set G) :=
  (le_sup_right : S R ≤ L ⊔ S R).trans
    ((L ⊔ S R).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ S R) (pCore 2 (L ⊔ S R : Subgroup G))))

/-- The Sylow group preserves the core: it preserves both the residual block
and its own characteristic Baumann subgroup. -/
theorem R_normalizes_Q (h : Configuration K A H R L) : R ≤ normalizer (Q R L : Set G) := by
  have hRL : R ≤ normalizer (L : Set G) :=
    (Chapter1.isSylowIn_iff.mp h.sylow).2.1.trans h.normalizes_L
  have hRS : R ≤ normalizer (S R : Set G) := h.le_A.trans h.normalizes_S
  exact ((le_inf hRL hRS).trans
    (normalizer_inf_normalizer_le_normalizer_sup L (S R))).trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ S R) (pCore 2 (L ⊔ S R : Subgroup G)))

/-- The actual block commutator layer is elementary abelian. -/
theorem elementary_U (h : Configuration K A H R L) : IsElementaryAbelian 2 (U L) := by
  let : IsElementaryAbelian 2 (ChapterC.blockU L) := h.block.chi.short.elementary
  exact IsElementaryAbelian.map L.subtype

/-- Centralizer reciprocity places the elementary block module centrally in `Q`. -/
theorem module_le_core (h : Configuration K A H R L) (hb : BaumannStructure H R L) :
    U L ≤ Q R L := by
  let : IsElementaryAbelian 2 (U L) := elementary_U h
  rw [hb.core_eq]
  exact le_inf hb.module_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)

/-- Conjugation carries the actual core centralizer to the corresponding
centralizer of the conjugate module, inside the same Baumann subgroup. -/
theorem conjugate_core_eq (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hx : x ∈ A) :
    (Q R L).map (MulAut.conj x).toMonoidHom =
      S R ⊓ centralizer ((U L).map (MulAut.conj x).toMonoidHom : Set G) := by
  have hS : (S R).map (MulAut.conj x).toMonoidHom = S R :=
    mem_normalizer_iff_map_conj_eq.mp (h.normalizes_S hx)
  rw [hb.core_eq, map_inf _ _ _ (MulAut.conj x).injective,
    hS, map_centralizer_equiv]

/-- C.5.6(4) from the earlier product calculations. Both cores have the same
Frattini subgroup as their intersection, since their supplements are central
and elementary. Also `Φ(Q) = Φ(D)` by `Q = UD`. -/
theorem frattini_invariant_of_factorization [Finite G]
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hx : x ∈ A) (hp : Factorization R L x) :
    (F R L).map (MulAut.conj x).toMonoidHom = F R L := by
  let e := MulAut.conj x
  let V := (U L).map e.toMonoidHom
  let Q' := (Q R L).map e.toMonoidHom
  let I := Q R L ⊓ Q'
  have huq := module_le_core h hb
  have hq'S : Q' ≤ S R := (conjugate_core_eq h hb hx).le.trans inf_le_left
  have hvq' : V ≤ Q' := map_mono huq
  have hqU : Q R L ≤ centralizer (U L : Set G) := hb.core_eq ▸ inf_le_right
  have huQ := le_centralizer_iff.mp hqU
  have hvQ' : V ≤ centralizer (Q' : Set G) := by
    rw [← map_centralizer_equiv]
    exact map_mono huQ
  have hdQ' : D R L ≤ Q' := by
    rw [show Q' = S R ⊓ centralizer (V : Set G) from conjugate_core_eq h hb hx]
    exact le_inf inf_le_left hp.centralizes
  have hqI : Q R L = U L ⊔ I := by
    apply le_antisymm
    · rw [hp.core]
      exact sup_le le_sup_left ((le_inf (hp.core ▸ le_sup_right) hdQ').trans le_sup_right)
    · exact sup_le huq inf_le_left
  have hq'I : Q' = V ⊔ I := by
    have he := supplement_intersection Q' V (Q R L) hvq'
      (hq'S.trans hp.span.le) ((hvq'.trans hq'S).trans (S_normalizes_Q R L))
    simpa only [I, inf_comm] using he
  have hu := elementary_U h
  let : IsElementaryAbelian 2 (U L) := hu
  have hv : IsElementaryAbelian 2 V := IsElementaryAbelian.map e.toMonoidHom
  have hQtwo : IsPGroup 2 (Q R L) := isPGroup_pCoreIn 2 (L ⊔ S R)
  have hqPhi := frattini_map_eq_of_central_elementary_supplement
    (Q R L) I (U L) hQtwo hu huQ hqI
  have hq'Phi := frattini_map_eq_of_central_elementary_supplement
    Q' I V (hQtwo.map e.toMonoidHom) hv hvQ' hq'I
  have hdPhi := frattini_map_eq_of_central_elementary_supplement
    (Q R L) (D R L) (U L) hQtwo hu huQ hp.core
  change ((frattini (D R L)).map (D R L).subtype).map e.toMonoidHom =
    (frattini (D R L)).map (D R L).subtype
  rw [← hdPhi, map_frattini_equiv]
  exact hq'Phi.trans hqPhi.symm

/-- The Frattini-zero hypothesis makes both displayed factors elementary.
This supplies the elementary candidates for the independent family calculations. -/
theorem elementary_candidates_of_frattini_eq_bot [Finite G]
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hp : Factorization R L x) (hf : F R L = ⊥) :
    IsElementaryAbelian 2 (Q R L) ∧ IsElementaryAbelian 2 (opposite R L x) := by
  have hDtwo : IsPGroup 2 (D R L) :=
    (Chapter1.isSylowIn_iff.mp h.sylow).1.to_le (inf_le_left.trans inf_le_left)
  let : Fact (IsPGroup 2 (D R L)) := ⟨hDtwo⟩
  have hphi : frattini (D R L) = ⊥ :=
    (map_injective (D R L).subtype_injective) (hf.trans (map_bot (D R L).subtype).symm)
  let : IsElementaryAbelian 2 (D R L) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  let : IsElementaryAbelian 2 (U L) := elementary_U h
  let : IsElementaryAbelian 2 ((U L).map (MulAut.conj x).toMonoidHom) :=
    IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  constructor
  · rw [hp.core]
    exact IsElementaryAbelian.sup_of_le_centralizer
      ((hp.core ▸ le_sup_right).trans (hb.core_eq ▸ inf_le_right))
  · exact IsElementaryAbelian.sup_of_le_centralizer hp.centralizes

private theorem map_symm_map (e : G ≃* G) (B : Subgroup G) :
    (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
  rw [map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  rw [he, map_id]

private theorem invariantFamily_map {T E : Subgroup G} (e : G ≃* G)
    (hR : R.map e.toMonoidHom = R) (hT : T.map e.toMonoidHom = T)
    (hE : E ∈ invariantFamily R T) : E.map e.toMonoidHom ∈ invariantFamily R T := by
  refine ⟨⟨hT ▸ map_mono hE.1.1, hE.1.2.1.map e.toMonoidHom, ?_⟩, ?_⟩
  · intro Y hY hYe
    have hback : Y.map e.symm.toMonoidHom ≤ T := by
      have hm := map_mono (f := e.symm.toMonoidHom) hY
      have he : T.map e.symm.toMonoidHom = T := by
        calc
          T.map e.symm.toMonoidHom = (T.map e.toMonoidHom).map e.symm.toMonoidHom :=
            congrArg (fun B : Subgroup G => B.map e.symm.toMonoidHom) hT.symm
          _ = T := map_symm_map e T
      rwa [he] at hm
    have hc := hE.1.2.2 _ hback (hYe.map e.symm.toMonoidHom)
    simpa only [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
      card_map_of_injective (f := e.toMonoidHom) e.injective] using hc
  · rw [← map_equiv_normalizer_eq]
    exact hR ▸ map_mono hE.2

/-- The second candidate is forced to be `Qˣ`: conjugation preserves the
invariant maximum family and moves `Q`. This handles both the two-member
family and the invariant members of the alternating-five four-member family. -/
theorem invariant_pair_of_candidates
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G))
    (hq : Q R L ∈ Stellmacher.elementaryAbelianMaxSubgroups (S R))
    (hcandidates : ∀ E ∈ invariantFamily R (S R), E = Q R L ∨ E = opposite R L x) :
    opposite R L x = (Q R L).map (MulAut.conj x).toMonoidHom ∧
      invariantFamily R (S R) = {Q R L, (Q R L).map (MulAut.conj x).toMonoidHom} := by
  have hqi : Q R L ∈ invariantFamily R (S R) := ⟨hq, R_normalizes_Q h⟩
  have hqxi : (Q R L).map (MulAut.conj x).toMonoidHom ∈ invariantFamily R (S R) :=
    invariantFamily_map (MulAut.conj x)
      (mem_normalizer_iff_map_conj_eq.mp (h.normalizes_R hx))
      (mem_normalizer_iff_map_conj_eq.mp (h.normalizes_S hx)) hqi
  have hne : (Q R L).map (MulAut.conj x).toMonoidHom ≠ Q R L := by
    intro he
    have hux : (U L).map (MulAut.conj x).toMonoidHom ≤ Q R L :=
      he ▸ map_mono (module_le_core h hb)
    exact hnc (hux.trans (hb.core_eq ▸ inf_le_right))
  have hop := ((hcandidates _ hqxi).resolve_left hne).symm
  refine ⟨hop, ?_⟩
  ext E
  constructor
  · intro hE
    rcases hcandidates E hE with he | he
    · simp [he]
    · simp [he, hop]
  · intro hE
    rcases Set.mem_insert_iff.mp hE with rfl | hE
    · exact hqi
    · have he := Set.mem_singleton_iff.mp hE
      exact he ▸ hqxi

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates
end
