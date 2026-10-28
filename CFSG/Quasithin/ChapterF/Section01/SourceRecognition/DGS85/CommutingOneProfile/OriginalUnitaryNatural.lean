module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryMarkedNatural

/-!
# Natural coordinates on the original alpha core

The source hypotheses and beta marking construct the short-path Frattini
and natural-action results in the reduced family. The literal inclusion
transports Phi(Q_alpha)=Z_alpha and the natural coordinate surjection,
including its exact kernel and conjugation by every original local element.
The coefficient field has order 2^(2m) for the supplied unitary degree m.

OriginalUnitarySource retains its historical four-walk API as a compatibility
wrapper. This result needs only its original source hypotheses, alpha actor
catalogue and beta marking; the path profiles remain a subsequent argument.
Source: DGS85, Groups and Graphs, (11.8)(e), p.176; reduction pp.95--96.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m))

include h hc hb hcomm Ma hm mark

theorem original_borel_unitary_alpha_natural_from_marking :
    let R := (Q F₀ (base F₀ false)).map (G₀).subtype
    let A := (Z F₀ (base F₀ false)).map (G₀).subtype
    let L := (graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype
    (frattini R).map R.subtype = A ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
        Nat.card k = 2^(2*m) ∧
        ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
          ∃ f : R →* Multiplicative (Fin 2 → k), Function.Surjective f ∧
            f.ker = A.subgroupOf R ∧
            ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
              (f y).toAdd = Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val (f x).toAdd := by
  let d := reducedFullEarlierLocalTheorems h
  let a := base F₀ false
  let b := base F₀ true
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_unitary_escaping_four_walk h hc hb hcomm Ma hm mark

  let eL := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have mark' : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) := by
    rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
    · exact Or.inl (hh.of_mulEquiv eqb)
    · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩
  have hphi := (source_unitary_alpha_frattini_from_marking (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) hm mark').1
  change (frattini (Q F₀ a)).map (Q F₀ a).subtype = Z F₀ a at hphi
  dsimp only
  refine ⟨?_,?_⟩
  · rw [frattini_image_map _ _ (G₀).subtype_injective,hphi]
  · obtain ⟨k,_,_,hk,⟨ea₀⟩⟩ := (original_unitary_centers_and_field h hc hb hcomm Ma hm mark).2.2.2
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hk)
    let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    let ea := ea₀.trans ep.symm
    obtain ⟨f,hf,hker,hact⟩ := source_unitary_alpha_natural_from_marking
      (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) d hc hb hcomm hbc hac (Ma.of_equiv eqa)
      hm mark' (eqa.trans ea) hk
    let eR := (Q F₀ a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    let f₀ := f.comp eR.symm.toMonoidHom
    refine ⟨k,inferInstance,inferInstance,inferInstance,hk,ea,f₀,hf.comp eR.symm.surjective,?_,?_⟩
    · ext x
      obtain ⟨x,rfl⟩ := eR.surjective x
      change f (eR.symm (eR x)) = 1 ↔ (eR x : G) ∈ (Z F₀ a).map (G₀).subtype
      rw [eR.symm_apply_apply]
      change x ∈ f.ker ↔ _
      rw [hker]
      constructor
      · intro hx
        exact mem_map_of_mem (G₀).subtype hx
      · rintro ⟨z,hz,he⟩
        have he' : z = (x : G₀) := (G₀).subtype_injective he
        change (x : G₀) ∈ Z F₀ a
        exact he' ▸ hz
    · intro l x y hy
      obtain ⟨l,rfl⟩ := eL.surjective l
      obtain ⟨x,rfl⟩ := eR.surjective x
      obtain ⟨y,rfl⟩ := eR.surjective y
      have he : (y : G₀) = (l : G₀) * (x : G₀) * (l : G₀)⁻¹ := by
        apply (G₀).subtype_injective
        exact hy
      have hh := hact l x y he
      change (f (eR.symm (eR y))).toAdd =
        Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 ((d.localGroup a).map (G₀).subtype)) (eL l))).val
          (f (eR.symm (eR x))).toAdd
      rw [eR.symm_apply_apply,eR.symm_apply_apply]
      exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
