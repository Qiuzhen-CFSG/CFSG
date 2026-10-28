module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalMathieuImage
public import Theory.Mathieu.M22.Properties.LocalA5Placement
public import Theory.Mathieu.SchurMultipliers.M23Kernel

/-!
# Literal Mathieu placements of a natural local escape

The M₂₂ image of the original local member is the native affine natural
actor, under an isomorphism of the original selected carrier's central
quotient. The proof transports the full normalizing Sylow and the actual
A₅ quotient, invokes the native local embedding theorem, and upgrades its
containment to equality using the checked order 960. The covering center
is retained in the literal projection.

In the M₂₃ branch, the proved trivial multiplier removes the entire center
of the original selected carrier. Its restriction to the local member is
therefore injective. Transporting the checked image calculations proves
that the original member itself is centerless of order 960, with elementary
two-core equal to its full commutator layer and of order sixteen.

The original-marker application discharges both model alternatives and
retains the same cubic prime, natural degree two, moving four-group and
proper inclusion in the selected carrier. These placements do not yet
exclude the embeddings or prove general Borel containment. Final
15.1.20(2)/15.1.22 assembly remains open, with original 15.1.14 and the
whole-core A₆ reconstruction retaining their existing producers.

Source: Aschbacher--Smith 15.1.20(2), 15.1.22, printed pp.1094--1100;
A.3.12(12), A.3.14(6), pp.47--49; I.1.1--3, pp.407--408.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.ChapterC Sporadic.Mathieu MathieuCode
open scoped MatrixGroups

private theorem m22_marking
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (q : A →* H) (hp : IsPGroup 2 q.ker) (hq : Function.Surjective q)
    (P : Sylow 2 A) (B : Subgroup A) [Group.IsPerfect B]
    (hPB : (P : Subgroup A) ≤ normalizer (B : Set A))
    (hb : IsL2EvenBlock B 2)
    (hE : IsElementaryAbelian 2 (pCore 2 (B.map q)))
    (h16 : Nat.card (pCore 2 (B.map q)) = 16)
    (hcard : Nat.card (B.map q) = 960)
    (e : H ≃* M22) :
    ∃ e' : H ≃* M22,
      ((B.map q).map e'.toMonoidHom).map m22ToPairStabilizer =
        M22ChapterH.Quintet.naturalActor.map M22Quintet.Q.subtype := by
  let D := B.map q
  let C := D.map e.toMonoidHom
  let R := (P.mapSurjective hq).mapSurjective (f := e.toMonoidHom) e.surjective
  let f := q.subgroupMap B
  have hfp : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hp.comap_subtype
  let eD := (f.pCoreQuotientEquiv (q.subgroupMap_surjective B) hfp).symm.trans
    hb.four_quotient_alternatingFive.some
  let ec : D ≃* C := e.subgroupMap D
  let eq : (D ⧸ pCore 2 D) ≃* (C ⧸ pCore 2 C) :=
    QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)
  let ecore : pCore 2 D ≃* pCore 2 C :=
    (ec.subgroupMap (pCore 2 D)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 ec))
  let : Group.IsPerfect D := Group.IsPerfect.map q
  let : Group.IsPerfect C := Group.IsPerfect.map e.toMonoidHom
  have hRC : (R : Subgroup M22) ≤ normalizer (C : Set M22) := by
    change ((P : Subgroup A).map q).map e.toMonoidHom ≤ _
    exact (map_mono ((map_mono hPB).trans (B.le_normalizer_map q))).trans
      (D.le_normalizer_map e.toMonoidHom)
  have hn : (C.subgroupOf (C ⊔ (R : Subgroup M22))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hRC)
  have he : IsElementaryAbelian 2 (pCore 2 C) := by
    let := hE
    exact IsElementaryAbelian.of_surjective ecore.toMonoidHom ecore.surjective
  obtain ⟨a,ha⟩ := M22LocalA5Placement.exists_marking R C hn.isSubnormal he
    ((Nat.card_congr ecore.toEquiv).symm.trans h16) (eq.symm.trans eD)
  refine ⟨e.trans a,?_⟩
  change ((D.map (e.trans a).toMonoidHom).map m22ToPairStabilizer) = _
  have hm : D.map (e.trans a).toMonoidHom = C.map a.toMonoidHom := by
    change D.map (a.toMonoidHom.comp e.toMonoidHom) =
      (D.map e.toMonoidHom).map a.toMonoidHom
    exact (map_map _ _ _).symm
  rw [hm]
  apply (eq_of_le_of_card_ge ha ?_).symm
  have hi : Function.Injective m22ToPairStabilizer :=
    fun _ _ h => m22Embedding_injective (congrArg Subtype.val h)
  rw [card_map_of_injective hi,card_map_of_injective a.injective,
    show C = D.map e.toMonoidHom from rfl,card_map_of_injective e.injective,hcard,
    card_map_of_injective M22Quintet.Q.subtype_injective,M22LocalA5Placement.natural_actor_card]

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original local image in the M₂₂ central quotient is exactly the
native natural affine actor, with the full covering projection retained. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_marking
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n)
    (model : Nonempty ((d.L ⧸ center d.L) ≃* M22)) :
    ∃ e : (d.L ⧸ center d.L) ≃* M22,
      (((K.subgroupOf d.L).map (QuotientGroup.mk' (center d.L))).map
        e.toMonoidHom).map m22ToPairStabilizer =
          M22ChapterH.Quintet.naturalActor.map M22Quintet.Q.subtype := by
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  obtain ⟨_,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  obtain ⟨hKL,_,_,_,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)
  let B := K.subgroupOf d.L
  let q := QuotientGroup.mk' (center d.L)
  have hB : IsL2EvenBlock B 2 := (hn ▸ hb : IsL2EvenBlock K 2).of_mulEquiv
    (subgroupOfEquivOfLe hKL.le).symm
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKL.le).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKL.le).symm.surjective
  obtain ⟨P,hP⟩ := s.component_sylow
  have hSN := s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hPB : (P : Subgroup d.L) ≤ normalizer (B : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro l hl k hk
    have hlS : l.val ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hl).1
    exact le_normalizer_iff.mp hSN l hlS k hk
  have hqp : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact (d.ordinary_center hL s.odd_core).2
  obtain ⟨hE,h16,_,_,_,hc,_⟩ := s.localFamily_linearTwo_mathieu_image (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  exact m22_marking q hqp (QuotientGroup.mk'_surjective _) P B hPB hB hE h16 hc model.some

/-- The trivial M₂₃ multiplier removes the full carrier center. Hence the
original local member, as well as its image, has elementary two-core of
order sixteen, trivial center and order 960. -/
theorem PreExclusionSource.localFamily_linearTwo_m23_uncovered
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n)
    (model : Nonempty ((d.L ⧸ center d.L) ≃* M23)) :
    center d.L = ⊥ ∧ center K = ⊥ ∧
      blockU K = pCore 2 K ∧ IsElementaryAbelian 2 (pCore 2 K) ∧
      Nat.card (pCore 2 K) = 16 ∧ Nat.card K = 960 ∧
      Nonempty (d.L ≃* M23) := by
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  have hzL : center d.L = ⊥ :=
    SchurMultipliers.m23_center_eq_bot_of_centralQuotientEquiv model.some
  obtain ⟨hKL,_,_,_,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by rcases hp with rfl | rfl <;> decide)
  let q := QuotientGroup.mk' (center d.L)
  let B := K.subgroupOf d.L
  let D := B.map q
  let f := q.subgroupMap B
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff _).mp
    ((QuotientGroup.ker_mk' _).trans hzL)
  have hfi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (hqi (congrArg Subtype.val he))
  let e : K ≃* D := (subgroupOfEquivOfLe hKL.le).symm.trans
    (MulEquiv.ofBijective f ⟨hfi,q.subgroupMap_surjective B⟩)
  obtain ⟨_,h16,hU,_,hz,hcard,_⟩ := s.localFamily_linearTwo_mathieu_image (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hzK : center K = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [FixedElementary.map_center,hz,Subgroup.map_bot]
  have hUK : blockU K = pCore 2 K := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective]
    exact hU
  have hE : IsElementaryAbelian 2 (pCore 2 K) := hUK ▸ hb.2.1.elementary
  have hc : Nat.card (pCore 2 K) = 16 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective (K := pCore 2 K),pCore_map_iso]
    exact h16
  let eL : d.L ≃* (d.L ⧸ center d.L) :=
    MulEquiv.ofBijective q ⟨hqi,QuotientGroup.mk'_surjective _⟩
  exact ⟨hzL,hzK,hUK,hE,hc,(Nat.card_congr e.toEquiv).trans hcard,
    ⟨eL.trans model.some⟩⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marked local family has literal native Mathieu placements.
The M₂₂ alternative retains the central quotient and identifies the exact
image with the native affine natural actor. In the M₂₃ alternative the
multiplier calculation removes the whole covering kernel, both from the
selected carrier and from the original natural local member. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_mathieu_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 ∧ K < d.L ∧
            ((∃ e : (d.L ⧸ center d.L) ≃* M22,
              (((K.subgroupOf d.L).map (QuotientGroup.mk' (center d.L))).map
                e.toMonoidHom).map m22ToPairStabilizer =
                  M22ChapterH.Quintet.naturalActor.map M22Quintet.Q.subtype) ∨
            (center d.L = ⊥ ∧ center K = ⊥ ∧
              blockU K = pCore 2 K ∧ IsElementaryAbelian 2 (pCore 2 K) ∧
              Nat.card (pCore 2 K) = 16 ∧ Nat.card K = 960 ∧
              Nonempty (d.L ≃* M23))) := by
  obtain ⟨d,hZ,hr,s,hfamily⟩ := h.source_preExclusion_local_natural_mathieu_carrier
    hG T hempty hM hmany hJ hu hne hfull m hp hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,hW,hcard,hKL,_,_,_,_,name,hname,model⟩ :=
    hfamily K hK hq hout n hb
  refine ⟨hp3,hn,hW,hcard,hKL,?_⟩
  rcases hname with rfl | rfl
  · exact .inl (s.localFamily_linearTwo_m22_marking (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb model)
  · exact .inr (s.localFamily_linearTwo_m23_uncovered (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb model)

end CFSG.Quasithin.Chapter15.Section01
