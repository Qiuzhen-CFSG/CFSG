module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearAmbientEscape
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreSurjective

/-!
# The original cubic normalizer residual in the linear triangle

For the scalar Cartan cubic E = X₁ = X₂, construct the literal
H = N_L(E)^∞. Coprime normalizer lifting makes N_L(E) cover L/O₂(L).
Perfectness of that quotient makes its residual cover it as well. The
two-group quotient N_L(E)/H kills E, so the original cubic lies in H.
Commutators with E lie both in E and O₂(L),
so E centralizes H. The restricted quotient map identifies O₂(H) with
H ∩ O₂(L) and gives the full SL₃(4) quotient, retaining its central cubic.

The inclusion also realizes the entire original action on V: O₂(L)
centralizes V, and H covers the original quotient. In particular [V,H]=V,
with the full fixed layer retained. The common-Q consumer applies these
facts to the same Cartan subgroup whose ambient normalizer escapes M.

This establishes the residual and its action at the start of the source
centralizer argument. The stronger factorization using O₂(L₁), the
two branches according to [O₂(H),H] (including the G.2.5 and B.4.14
comparison), original SL₃(4) exclusion, common-normal existence, both
triangle orientations and full 11.1.1--3 remain with
qt-d-1222-natural-relative-components. Original earlier-source inputs
retain their producers and final discharge by
qt-d-1222-natural-local-geometry. No projective module extension is chosen.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 11.1.2,
printed p.763, the construction of L_X₁ and the subsequent module argument.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
open scoped commutatorElement

private theorem cubic_residual_data
    {G : Type*} [Group G] [Finite G] (L E : Subgroup G) [Group.IsPerfect L]
    (hEL : E ≤ L) (hE : IsPGroup 3 E)
    (hcentral : E ≤ Closure.coreQuotientCentralizer L) :
    E ≤ localResidual L E ∧
    localResidual L E ≤ centralizer (E : Set G) ∧
    Function.Surjective ((QuotientGroup.mk' (pCore 2 L)).comp
      (inclusion ((localResidual_le E).trans inf_le_left))) ∧
    (localResidual L E).pCoreIn 2 = localResidual L E ⊓ L.pCoreIn 2 ∧
    localResidual L E ⊔ L.pCoreIn 2 = L := by
  let N := L ⊓ normalizer (E : Set G)
  let H := localResidual L E
  let q := QuotientGroup.mk' (pCore 2 L)
  let f : N →* L ⧸ pCore 2 L := q.comp (inclusion (show N ≤ L from inf_le_left))
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hfker : IsPGroup 2 f.ker := hk.comap_of_injective _ (inclusion_injective _)
  have hc : (E.subgroupOf L).map q ≤ center (L ⧸ pCore 2 L) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro z
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
    obtain ⟨r,hr,he⟩ := Closure.coreQuotientCentralizer_commutator (hcentral hx) y.property
    have he' : r = ⁅x,y⁆ := Subtype.ext he
    have hh : q ⁅x,y⁆ = 1 := by
      rw [←he']
      exact (QuotientGroup.eq_one_iff _).mpr hr
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
    exact hh.symm
  have hn : Function.Surjective f := by
    let : Fact (IsPGroup 3 (E.subgroupOf L)) := ⟨hE.comap_subtype⟩
    have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
      obtain ⟨n,hn⟩ := hk.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    have he := normalizer_map_eq_of_coprime_kernel 3 (E.subgroupOf L) q
      (QuotientGroup.mk'_surjective _) hcop
    have htop : normalizer ((E.subgroupOf L).map q : Set (L ⧸ pCore 2 L)) = ⊤ := by
      apply top_unique
      rw [←centralizer_eq_top_iff_subset.mpr hc]
      exact Subgroup.centralizer_le_normalizer _
    rw [htop] at he
    intro z
    obtain ⟨x,hx,hxz⟩ := he.le (mem_top z)
    have hx' : (x : G) ∈ normalizer (E : Set G) := by
      rw [←subgroupOf_normalizer_eq hEL] at hx
      exact hx
    exact ⟨⟨x,⟨x.property,hx'⟩⟩,hxz⟩
  have hr : (solvableResidual N).map f = ⊤ := by
    rw [map_solvableResidual_eq f hn,solvableResidual_eq_top]
  have hgen : solvableResidual N ⊔ f.ker = ⊤ := by
    rw [←comap_map_eq,hr,comap_top]
  have hquot : IsPGroup 2 (N ⧸ solvableResidual N) :=
    isPGroup_quotient_of_sup_eq_top _ _ hfker hgen
  have hEN : E ≤ N := le_inf hEL E.le_normalizer
  have hEH : E ≤ H := by
    let π := QuotientGroup.mk' (solvableResidual N)
    have hz : (E.subgroupOf N).map π = ⊥ := by
      apply disjoint_self.mp
      exact (hE.comap_subtype.map π).disjoint_of_coprime
        (hquot.to_subgroup _) (by decide)
    intro x hx
    have hxr : (⟨x,hEN hx⟩ : N) ∈ solvableResidual N := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact hz.le (mem_map_of_mem π hx)
    exact ⟨⟨x,hEN hx⟩,hxr,rfl⟩
  have hNE : N ≤ centralizer (E : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    have hEc : Disjoint E (L.pCoreIn 2) :=
      hE.disjoint_of_coprime (isPGroup_pCoreIn 2 L) (by decide)
    apply (le_inf (le_normalizer_iff_commutator_le_right.mp
      (show N ≤ normalizer (E : Set G) from inf_le_right)) ?_).trans hEc.le_bot
    rw [commutator_comm]
    exact commutator_le.mpr fun x hx y hy =>
      Closure.coreQuotientCentralizer_commutator (hcentral hx) hy.1
  let g := q.comp (inclusion (show H ≤ L from (localResidual_le E).trans inf_le_left))
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨x,hx,hxz⟩ := hr.ge (mem_top z)
    exact ⟨⟨x,mem_map_of_mem N.subtype hx⟩,hxz⟩
  have hgker : IsPGroup 2 g.ker := hk.comap_of_injective _ (inclusion_injective _)
  have hker : g.ker = pCore 2 H := by
    have hh := g.comap_pCore_of_ker_isPGroup hg hgker
    rw [pCore_quotient_pCore_eq_bot] at hh
    exact hh
  refine ⟨hEH,(localResidual_le E).trans hNE,hg,?_,?_⟩
  · change (pCore 2 H).map H.subtype = H ⊓ L.pCoreIn 2
    rw [←hker]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,⟨inclusion ((localResidual_le E).trans inf_le_left) a,
        (QuotientGroup.eq_one_iff _).mp ha,rfl⟩⟩
    · rintro ⟨hx,y,hy,rfl⟩
      refine ⟨⟨y,hx⟩,?_,rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr hy
  · have hm : (H.subgroupOf L).map q = ⊤ := by
      apply top_unique
      intro y _
      obtain ⟨x,rfl⟩ := hg y
      exact mem_map_of_mem q x.property
    have hh := congrArg (comap q) hm
    rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
    have hm := congrArg (map L.subtype) hh
    change H ⊔ (pCore 2 L).map L.subtype = L
    simpa only [Subgroup.map_sup,
      map_subgroupOf_eq_of_le (show H ≤ L from (localResidual_le E).trans inf_le_left),
      ←MonoidHom.range_eq_map,range_subtype] using hm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The source cubic normalizer residual contains the original cubic centrally
and covers the full SL₃ quotient through the original inclusion. -/
theorem linear_four_cubic_normalizer_residual
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    E ≤ H ∧ H ≤ centralizer (E : Set G) ∧
    H.pCoreIn 2 = H ⊓ L.pCoreIn 2 ∧ H ⊔ L.pCoreIn 2 = L ∧
    ∃ e : (H ⧸ pCore 2 H) ≃* (Coordinates.sl3 m).ModelGroup,
      ∀ h : H, e (QuotientGroup.mk' (pCore 2 H) h) =
        (Coordinates.sl3 m).quotientMap
          (inclusion ((localResidual_le E).trans inf_le_left) h) := by
  let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  let H := localResidual L E
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  have hE : IsPGroup 3 E := IsPGroup.of_card (p := 3) (n := 1) (by simpa only [E,pow_one] using hcard)
  have hcentral : E ≤ Closure.coreQuotientCentralizer L :=
    (linear_four_cartan_section_kernel D S m hd f hX 0).le.trans inf_le_right
  obtain ⟨hEH,hHC,honto,hcore,hcover⟩ := cubic_residual_data L E
    (inf_le_left.trans (hX.1.trans inf_le_left)) hE hcentral
  refine ⟨hEH,hHC,hcore,hcover,?_⟩
  let q := (QuotientGroup.mk' (pCore 2 L)).comp
    (inclusion (show H ≤ L from (localResidual_le E).trans inf_le_left))
  have hqker : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hk : q.ker = pCore 2 H := by
    have hh := q.comap_pCore_of_ker_isPGroup honto hqker
    rw [pCore_quotient_pCore_eq_bot] at hh
    exact hh
  let e : (H ⧸ pCore 2 H) ≃* (L ⧸ pCore 2 L) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q honto)
  exact ⟨e.trans (Coordinates.sl3 m).groupEquiv,fun _ => rfl⟩

/-- The residual realizes the entire original action on V, including its
fixed layer. This uses the literal inclusion and the original two-core,
which centralizes the full chosen subgroup. -/
theorem linear_four_cubic_residual_full_action
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    (∀ l ∈ L, ∃ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ = l * v * l⁻¹) ∧ V = ⁅V,H⁆ := by
  let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  let H := localResidual L E
  have hHL : H ≤ L := (localResidual_le E).trans inf_le_left
  obtain ⟨_,_,_,_,e,he⟩ := linear_four_cubic_normalizer_residual D S m f hd hX hcard
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes (p := 2) (Y := L)
      (L := L ⊔ (T : Subgroup G)) le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  let a : L →* MulAut V := V.normalizerMonoidHom.comp (inclusion D.normalizes)
  have ha : pCore 2 L ≤ a.ker := by
    intro l hl
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (l : G) * (v : G) * (l : G)⁻¹ = (v : G)
    have hc : (v : G) * (l : G) = (l : G) * (v : G) :=
      hcore (mem_map_of_mem L.subtype hl) (v : G) v.property
    rw [←hc,mul_inv_cancel_right]
  let b := QuotientGroup.lift (pCore 2 L) a ha
  have hact : ∀ l ∈ L, ∃ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ = l * v * l⁻¹ := by
    intro l hl
    obtain ⟨z,hz⟩ := e.surjective ((Coordinates.sl3 m).quotientMap ⟨l,hl⟩)
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) z
    have hq := (he h).symm.trans hz
    have hq' := (Coordinates.sl3 m).groupEquiv.injective hq
    have hh : a (inclusion hHL h) = a ⟨l,hl⟩ := congrArg b hq'
    refine ⟨h,h.property,?_⟩
    intro v hv
    exact congrArg (fun c : MulAut V => (c ⟨v,hv⟩ : G)) hh
  refine ⟨hact,le_antisymm ?_ ?_⟩
  · conv_lhs => rw [D.eq_commutator,commutator_comm]
    apply commutator_le.mpr
    intro l hl v hv
    obtain ⟨h,hh,hv'⟩ := hact l hl
    have he' : ⁅l,v⁆ = ⁅h,v⁆ := by
      simp only [commutatorElement_def]
      rw [hv' v hv]
    rw [he']
    exact commutator_comm H V ▸ commutator_mem_commutator hh hv
  · exact (commutator_mono le_rfl hHL).trans_eq D.eq_commutator.symm

/-- Apply the construction at the original common-Q linear triangle. The
ambient cubic normalizer escapes M while the literal residual inside L
retains its full central SL₃(4) quotient and original two-core intersection. -/
theorem linear_triangle_centralizer_setup_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    E ≤ H ∧ H ≤ centralizer (E : Set G) ∧
    Source.IsSL (H ⧸ pCore 2 H) 3 4 ∧
    H.pCoreIn 2 = H ⊓ L.pCoreIn 2 ∧ H ⊔ L.pCoreIn 2 = L ∧
    (∀ l ∈ L, ∃ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ = l * v * l⁻¹) ∧
    V = ⁅V,H⁆ ∧ ¬ normalizer (E : Set G) ≤ normalizer (L : Set G) := by
  have hc : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3 := by
    rwa [linear_four_cartan_kernels_eq D S m hd f hX]
  obtain ⟨hEH,hHC,hcore,hcover,e,he⟩ :=
    linear_four_cubic_normalizer_residual D S m f hd hX hc
  have hout := linear_triangle_cubic_normalizers_not_le_original_maximal_of_common_normal
    D S m f hd hfix hX hK hLK hK₀ hK₀K hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ
  obtain ⟨hact,hmoved⟩ := linear_four_cubic_residual_full_action D S m f hd hX hc
  exact ⟨hEH,hHC,⟨S.field.Carrier,inferInstance,inferInstance,
    by simpa [hd] using S.field.card_eq,⟨e⟩⟩,hcore,hcover,hact,hmoved,hout.1⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
