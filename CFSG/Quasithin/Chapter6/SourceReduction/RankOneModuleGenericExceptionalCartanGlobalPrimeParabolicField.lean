module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticResidual
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.SpecificGroups.SL2.FieldCardinality
public import Theory.GroupTheory.CComponent.LocalImageEquality

/-!
# The selected parabolic's field in the symplectic residual row

The source identity S ∩ O²(H) = T ∩ O²(H) places the selected right
factor locally at a full Sylow of the literal residual. It need not be
an H-component. After quotienting by the residual two-core, local
component minimality preserves properness. The genuine symplectic
point/plane placement theorem identifies the image's intrinsic two-core
quotient with SL₂ over the original residual field.

The restricted quotient map has two-group kernel, so this identification
returns to R/O₂(R). Comparing two SL₂ orders proves equality of the right
factor and residual field degrees. In particular an A₅ right factor
forces Sp₄(4), constructs the original Hall subgroup B as E₉, and supplies
the actual degree-two normalization conclusion. The field of L/O₂(L)
is kept separate. The same local-to-global owner retains the other
source models, higher-degree and zero-core branches, and final assembly.

Source: Aschbacher–Smith A.3.12, 5.1.10 and 5.2.2,
printed pp.47–48,634,648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem symplectic_local_quotient
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {R : Subgroup X}
    (hR : R ∈ ChapterA.Section03.localCComponents S)
    (htop : (⊤ : Subgroup X).IsCComponent) (hne : R ≠ ⊤)
    {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp (X ⧸ pCore 2 X) 2 (2 ^ f)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e0 := e.trans EvenProjective.equiv.symm
  let q := e0.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e0.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    ext x
    exact e0.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  let : Group.IsNilpotent q.ker := hk ▸ pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  let P := S.mapSurjective hq
  have hl : R.map q ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hR q
  have hproper : R.map q ≠ ⊤ := by
    intro he
    apply hne
    apply local_cComponent_eq_of_map_eq hR htop le_top q
      (hk ▸ pCore_isPGroup.le_sylow_of_normal S)
    simpa only [map_top_of_surjective q hq] using he
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    hF hf P (R.map q) hl hproper
  let a := (MulAut.conj g).subgroupMap (R.map q)
  let r := q.subgroupMap R
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let eR := r.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective R) hr
  let ea := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have he : Nonempty ((R ⧸ pCore 2 R) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
    rcases hg with hp | hp
    · let ep := MulEquiv.subgroupCongr hp
      let eqp := QuotientGroup.congr _ _ ep (pCore_map_iso 2 ep)
      exact ⟨eR.trans (ea.trans (eqp.trans (pointLocalCoreQuotientEquiv hF hf)))⟩
    · let ep := MulEquiv.subgroupCongr hp
      let eqp := QuotientGroup.congr _ _ ep (pCore_map_iso 2 ep)
      exact ⟨eR.trans (ea.trans (eqp.trans (planeLocalCoreQuotientEquiv hF hf)))⟩
  exact ⟨F,inferInstance,inferInstance,hF,
    he.map (fun a => a.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)))⟩

/-- The original residual has a full Sylow at which the selected factor is local. -/
theorem LocalData.right_local_in_residual
    {T : Sylow 2 G} {L H B D R : Subgroup G}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H) :
    ∃ S : Sylow 2 (residual H),
      (S : Subgroup (residual H)) = (T : Subgroup G).subgroupOf (residual H) ∧
      R.subgroupOf (residual H) ∈ ChapterA.Section03.localCComponents S := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T (residual H)
    (hTH.trans (le_normalizer_residual H))
  have he : (normalizingSylow T R).subgroupOf (residual H) =
      (T : Subgroup G).subgroupOf (residual H) := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      have hxt : (x : G) ∈ Global.sourceS L H ⊓ residual H := by
        rw [d.S_intersection_residual]
        exact ⟨hx,x.property⟩
      exact ⟨hx,d.S_normalizes_right hxt.1⟩
  refine ⟨S,hS,?_⟩
  rw [hS,←he]
  exact ChapterA.Section03.SourceEmbeddings.local_restrict d.right_component d.right_le_residual

/-- The intrinsic selected-factor quotient has the original symplectic residual field. -/
theorem LocalData.symplectic_residual_right_quotient
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 3 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let e0 := e.trans EvenProjective.equiv.symm
  let : IsQuasisimple (Sp F) := CentralCovers.Even.isQuasisimple hlarge
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv e0.symm
  let eK : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eqK := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let : IsQuasisimple ((residual H) ⧸ pCore 2 (residual H)) :=
    IsQuasisimple.of_mulEquiv eqK
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (residual H)) pCore_isPGroup (isPPerfect_embedded_pResidual 2 H)
  obtain ⟨S,_,hl⟩ := d.right_local_in_residual hTH
  have hn : R.subgroupOf (residual H) ≠ ⊤ := fun he => hR.not_ge (subgroupOf_eq_top.mp he)
  have hs := symplectic_local_quotient S hl ht hn hf
    (show ClassicalGroup.IsPSp ((residual H) ⧸ pCore 2 (residual H)) 2 (2 ^ f) from
      ⟨F,inferInstance,inferInstance,hF,⟨eqK.symm.trans e⟩⟩)
  let er := subgroupOfEquivOfLe d.right_le_residual
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  exact hs.of_mulEquiv eqr.symm

private theorem binary_degree_eq
    {X : Type*} [Group X] {f m : ℕ}
    (hf : ClassicalGroup.IsPSL X 2 (2 ^ f))
    (hm : ClassicalGroup.IsPSL X 2 (2 ^ m)) : f = m := by
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hf
  obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let e := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).trans
    (eF.symm.trans (eE.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm))
  exact Matrix.SL2.field_degree_eq_of_equiv e (by decide) hF hE

/-- The residual and selected parabolic have the same field degree,
proved through their literal two-core quotients. This compares neither
degree with the unrelated degree of the original left factor L. -/
theorem LocalData.symplectic_residual_degree_eq
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f m : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) : f = m :=
  binary_degree_eq (d.symplectic_residual_right_quotient hTH hR hf hm) hr

/-- An actual A₅ parabolic factor forces the original symplectic residual
to be Sp₄(4), and constructs the prescribed Hall subgroup B as E₉. -/
theorem LocalData.A5_right_symplectic_hall_plane
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n f : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    f = 2 ∧ ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      IsElementaryAbelian 3 B ∧ Nat.card B = 9 := by
  have hf2 := d.symplectic_residual_degree_eq hH.1.1.2 hR hf hm (m := 2) hA5
  have hm4 : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 := by
    simpa only [hf2,show (2 : ℕ) ^ 2 = 4 by norm_num] using hm
  exact ⟨hf2,hm4,c.right_cubic_plane_of_symplectic_residual h.sylow_normalizes hH hgen hm4⟩

/-- In the nonzero-core prime configuration, strictness is supplied by
the original escaping actor. No component-of-H hypothesis is needed. -/
theorem LocalData.A5_right_symplectic_prime_hall
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    f = 2 ∧ ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧ p = 5 := by
  obtain ⟨hf2,hm4,hB,hcard⟩ := d.A5_right_symplectic_hall_plane h hH hgen c
    (d.right_lt_residual hH.1.1.2 c hd hz) hf hm hA5
  exact ⟨hf2,hm4,hB,hcard,d.A5_right_symplectic_residual_actor_prime h hH hgen c hd hf hm hA5⟩

/-- The original degree-two normalization conclusion in the selected
A₅ parabolic row, with the residual field comparison discharged. -/
theorem LocalData.cartan_normalizes_of_A5_symplectic_degree_two
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {f : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hcontrol : CartanLocalControl A H) (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    A ≤ normalizer (residual H : Set G) := by
  have hf2 := d.symplectic_residual_degree_eq hH.1.1.2 hR hf hm (m := 2) hA5
  exact h.cartan_normalizes_of_symplectic_residual_small_degree hH hgen c hcontrol
    (Or.inl rfl) hf (by rw [hf2]) hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
