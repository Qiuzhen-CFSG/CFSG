module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalFieldFour
public import CFSG.Quasithin.Chapter5.Section03
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore

/-!
# Ambient central-involution bounds for the G₂ completion

The center of the short G₂ local factor is contained in the highest-root
group. The literal split torus scales this root parameter transitively on
nonzero elements. Transport through the original right parabolic isomorphism
therefore proves transitivity on the center of K = O²(H), with its actual
conjugation action retained.

Characteristic two puts Z(K) inside the original Sylow T. Its normality
under T supplies a central involution of T in Z(K). Original uniqueness
for KT bounds the ambient centralizer of that involution by N_G(K), and
the proved orbit transports the bound to every central involution of K.
Original uniqueness over L supplies the left bound directly. Thus both
central-involution bounds used in 5.3.3 are proved for this row, including
field order four, with no extra action or fixed-point premise.

The Chapter12 companion supplies these bounds together with the literal
normalizer conditions on the same prepared pair. Concrete amalgam comparison
remains an explicit input, and original uniqueness remains in Preparation.
Exhaustive F.1.12 comparison and concrete and ambient completion recognition
are still obligations of the generic-global owner; this proves no GlobalExit.
Source: Aschbacher–Smith 5.3.1–3, printed pp.658–659, and F.1.12(I)(3),
pp.262–264 (`refs/quasithin.pdf`). The root calculations use the existing
licensed ATLAS port without changing its conventions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- A transitive local action on the nonidentity center transports the
centralizer bound from an original Sylow-central involution. -/
theorem center_orbit_centralizer_bound {T : Sylow 2 G} {K P : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hchar : HasCharacteristicTwo K) (hPN : P ≤ normalizer (K : Set G))
    (hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ (T : Subgroup G) ≤ M →
      M = normalizer (K : Set G))
    (horbit : ∀ x ∈ (center K).map K.subtype, x ≠ 1 →
      ∀ y ∈ (center K).map K.subtype, y ≠ 1 → ∃ g ∈ P, y = g*x*g⁻¹)
    (z : G) (hz : z ∈ (center K).map K.subtype) (hz2 : orderOf z = 2) :
    centralizer ({z} : Set G) ≤ normalizer (K : Set G) := by
  let Z := (center K).map K.subtype
  have hZT : Z ≤ (T : Subgroup G) := by
    have hZQ : center K ≤ pCore 2 K :=
      (center_le_centralizer (pCore 2 K : Set K)).trans hchar
    obtain ⟨U,hU⟩ := exists_sylow_component hTK
    exact (map_mono hZQ).trans ((pCoreIn_le_sylow K U).trans (hU ▸ inf_le_left))
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    hTK.trans (normalizer_le_normalizer_characteristic_image K (center K))
  let N := Z.subgroupOf (T : Subgroup G)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hTZ
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr (by
    intro he
    have : (⟨z,hZT hz⟩ : (T : Subgroup G)) ∈ N := hz
    rw [he,mem_bot] at this
    exact hz1 (congrArg Subtype.val this))
  let : Fact (IsPGroup 2 (T : Subgroup G)) := ⟨T.isPGroup'⟩
  obtain ⟨C,_,hCN,hcard,hCZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N inferInstance
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hcard])
  let x : G := c.val.val
  have hxZ : x ∈ Z := hCN c.property
  have hx2 : orderOf x = 2 := by simpa only [x,Subgroup.orderOf_coe] using hc
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx2
  have hKC : K ≤ centralizer ({x} : Set G) := by
    obtain ⟨a,ha,he⟩ := hxZ
    intro k hk
    apply mem_centralizer_singleton_iff.mpr
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨k,hk⟩)
  have hTC : (T : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp (hCZ c.property) ⟨t,ht⟩))
  obtain ⟨M,hCM,hM⟩ := Finite.exists_le_maximal (isTwoLocal_involution_centralizer hx2)
  have hM' := hunique M hM ((sup_le hKC hTC).trans hCM)
  have hxC : centralizer ({x} : Set G) ≤ normalizer (K : Set G) := hM' ▸ hCM
  obtain ⟨g,hg,he⟩ := horbit x hxZ hx1 z hz hz1
  exact Chapter5.Section03.centralizer_le_of_conjugate _ g (hPN hg) he hxC

open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
private theorem g2_center_mem_highestRoot
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {z : Model F} (hz : z ∈ (center (local₁ (F := F))).map local₁.subtype) :
    z ∈ highestRoot (F := F) := by
  obtain ⟨a,ha,rfl⟩ := hz
  have hLP : local₁ (F := F) ≤ parabolic₁ := le_sup_left.trans_eq local₁_sup_borel
  have hc : (⟨a.val,hLP a.property⟩ : parabolic₁ (F := F)) ∈
      centralizer ((radical₁ (F := F)).subgroupOf parabolic₁ : Set (parabolic₁ (F := F))) := by
    apply mem_centralizer_iff.mpr
    intro r hr
    apply Subtype.ext
    change (r.val : Model F) * a.val = a.val * r.val
    exact congrArg (fun k : local₁ (F := F) => k.val)
      (mem_center_iff.mp ha ⟨r.val,radical₁_le_local₁ hr⟩)
  have har : a.val ∈ radical₁ (F := F) := EvenLocal.short_radical_selfCentralizing hc
  rw [←center_map_eq_highestRoot (radical₁ (F := F)) le_rfl
    (fiveRootSubgroup_le_unipotent _ _)]
  refine ⟨⟨a.val,har⟩,mem_center_iff.mpr (fun r => ?_),rfl⟩
  apply Subtype.ext
  change (r.val : Model F) * a.val = a.val * r.val
  exact congrArg (fun k : local₁ (F := F) => k.val)
    (mem_center_iff.mp ha ⟨r.val,radical₁_le_local₁ r.property⟩)

private theorem g2_center_orbit
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (x y : Model F) (hx : x ∈ (center (local₁ (F := F))).map local₁.subtype)
    (hy : y ∈ (center (local₁ (F := F))).map local₁.subtype) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ parabolic₁ (F := F), y = g*x*g⁻¹ := by
  obtain ⟨a,ha⟩ := g2_center_mem_highestRoot hx
  obtain ⟨b,hb⟩ := g2_center_mem_highestRoot hy
  have ha0 : a.toAdd ≠ 0 := by intro he; apply hx1; rw [←ha]; change rootA a.toAdd = 1; simp [he]
  have hb0 : b.toAdd ≠ 0 := by intro he; apply hy1; rw [←hb]; change rootA b.toAdd = 1; simp [he]
  let u : Fˣ := Units.mk0 (b.toAdd / a.toAdd) (div_ne_zero hb0 ha0)
  refine ⟨torus u 1,borel_le_parabolic₁ (mem_sup_right ⟨(u,1),rfl⟩),?_⟩
  rw [←ha,←hb]
  change rootA b.toAdd = torus u 1 * rootA a.toAdd * (torus u 1)⁻¹
  rw [torus_rootA]
  simp [u,ha0]

omit [Finite G] in
/-- Transport center transitivity through the literal parabolic map and
its specified image of the local factor. -/
theorem center_orbit_transport
    {X : Type*} [Group X] {K P : Subgroup G} {R Q : Subgroup X}
    (hKP : K ≤ P) (e : P ≃* Q)
    (hR : (K.subgroupOf P).map (Q.subtype.comp e.toMonoidHom) = R)
    (horbit : ∀ x ∈ (center R).map R.subtype, x ≠ 1 →
      ∀ y ∈ (center R).map R.subtype, y ≠ 1 → ∃ g ∈ Q, y = g*x*g⁻¹) :
    ∀ x ∈ (center K).map K.subtype, x ≠ 1 →
      ∀ y ∈ (center K).map K.subtype, y ≠ 1 → ∃ g ∈ P, y = g*x*g⁻¹ := by
  let f := Q.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp e.injective
  have hc (x : G) (hx : x ∈ (center K).map K.subtype) :
      ∃ a : P, (a : G) = x ∧ f a ∈ (center R).map R.subtype := by
    obtain ⟨k,hk,rfl⟩ := hx
    let a : P := ⟨k,hKP k.property⟩
    have haR : f a ∈ R := hR ▸ mem_map_of_mem f k.property
    refine ⟨a,rfl,⟨⟨f a,haR⟩,?_,rfl⟩⟩
    apply mem_center_iff.mpr
    intro r
    have hr : r.val ∈ (K.subgroupOf P).map f := hR.symm ▸ r.property
    obtain ⟨b,hb,he⟩ := hr
    apply Subtype.ext
    change r.val * f a = f a * r.val
    rw [←he,←map_mul,←map_mul]
    apply congrArg f
    apply Subtype.ext
    exact congrArg (fun k : K => k.val) (mem_center_iff.mp hk ⟨b,hb⟩)
  intro x hx hx1 y hy hy1
  obtain ⟨a,ha,hac⟩ := hc x hx
  obtain ⟨b,hb,hbc⟩ := hc y hy
  have ha1 : f a ≠ 1 := by
    intro he
    exact hx1 (ha ▸ congrArg Subtype.val (hf (he.trans (map_one f).symm)))
  have hb1 : f b ≠ 1 := by
    intro he
    exact hy1 (hb ▸ congrArg Subtype.val (hf (he.trans (map_one f).symm)))
  obtain ⟨g,hg,he⟩ := horbit (f a) hac ha1 (f b) hbc hb1
  let c : P := e.symm ⟨g,hg⟩
  have hfc : f c = g := congrArg Subtype.val (e.apply_symm_apply ⟨g,hg⟩)
  refine ⟨c,c.property,?_⟩
  have hh : b = c*a*c⁻¹ := hf (by simpa only [map_mul,map_inv,hfc] using he)
  have hh' : (b : G) = (c : G) * (a : G) * (c : G)⁻¹ := congrArg Subtype.val hh
  simpa only [ha,hb] using hh'

/-- The original right parabolic is transitive on the nonidentity center of K
through its literal G₂ comparison, including field order four. -/
theorem Preparation.g2_right_center_orbit
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∀ x ∈ (center (residual H)).map (residual H).subtype, x ≠ 1 →
      ∀ y ∈ (center (residual H)).map (residual H).subtype, y ≠ 1 →
        ∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
          y = g*x*g⁻¹ := by
  have hF := (d.g2_local_structure h hTH hp F he).1
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  rcases he with he | he
  · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
  obtain ⟨e⟩ := he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  have hres : (residual H).subgroupOf P = solvableResidual P := by
    have hr : (solvableResidual P).map P.subtype = residual H :=
      d.parabolic_residuals h hTH hp 1
    rw [←hr]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  apply center_orbit_transport (R := local₁ (F := F)) hKP e.right
  · rw [hres,←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    exact HigherFieldResiduals.parabolic₁_residual hq
  · intro x hx hx1 y hy hy1
    exact g2_center_orbit x y hx hy hx1 hy1

/-- Original uniqueness over L controls every central involution of L. -/
theorem Preparation.left_central_involution_centralizer
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (z : G) (hz : z ∈ (center L).map L.subtype) (hz2 : orderOf z = 2) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  have hLC : L ≤ centralizer ({z} : Set G) := by
    obtain ⟨a,ha,rfl⟩ := hz
    intro l hl
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp ha ⟨l,hl⟩))
  obtain ⟨M,hCM,hM⟩ := Finite.exists_le_maximal (isTwoLocal_involution_centralizer hz2)
  exact d.unique_left M hM (hLC.trans hCM) ▸ hCM

/-- Both central-involution bounds required in source 5.3.3 hold for the
actual G₂ pair. No fixed-point or center-transitivity premise is added. -/
theorem Preparation.g2_central_involution_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  intro i
  fin_cases i
  · exact d.left_central_involution_centralizer
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hK := d.g2_right_maximal_all h hH hp F he
  have hu := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_unique
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
      (le_componentOrbit _ _)
  rw [ho] at hu
  have hc := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hK.1
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_centralizer_bound hTK hc hPN hu
    (d.g2_right_center_orbit h hH.1.1.2 hp F he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
