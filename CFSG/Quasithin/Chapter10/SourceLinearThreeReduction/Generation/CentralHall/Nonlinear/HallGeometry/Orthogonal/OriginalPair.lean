module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Orthogonal.PairAction
public import Theory.Representation.BinaryConjugationSection.PairedAction

/-!
# Original paired moved-module actions

The crossed centralization in the source module geometry lets the actual
component-orbit action on a moved factor pass through the first marked simple
quotient. An outside Sylow conjugation exchanges the two quotient projections.
The central Hall hypothesis fixes both components of the central diagonal.
Source: Aschbacher--Smith 10.1.1--2, printed pp.741--742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)

/-- Crossed centralization in the original (unconjugated) orientation. -/
theorem moved_centralizes_partner (geometry : ModuleGeometry D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    L.map (MulAut.conj t).toMonoidHom ≤ centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hi : t⁻¹ ∉ normalizer (L : Set G) := fun h => htn (by simpa using (normalizer (L : Set G)).inv_mem h)
  have hh := geometry.crossed t⁻¹ ((T : Subgroup G).inv_mem ht) hi
  rintro _ ⟨l,hl,rfl⟩ w hw
  have he := hh (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hw) l hl
  have he' := congrArg (MulAut.conj t) he
  simpa only [map_mul,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
    mul_assoc, mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel_right,mul_inv_cancel,inv_mul_cancel,one_mul,mul_one] using he'.symm

include c in
/-- The original orbit preserves the literal moved factor. -/
theorem orbit_normalizes_moved : localOrbit T L ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      ((localOrbit T L).le_normalizer hr)),
    mem_normalizer_iff_map_conj_eq.mp (source_nonnormal_orbit_le_normalizer D c.nonnormal hr)]

/-- Original Sylow component stabilizers preserve the moved factor. -/
theorem stabilizer_normalizes_moved :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T hs.1)),
    mem_normalizer_iff_map_conj_eq.mp hs.2]

/-- The source geometry makes the moved group elementary abelian. -/
theorem moved_elementary (geometry : ModuleGeometry D) : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) := by
  let := D.module_elementary
  have hWV : ⁅D.fullModule,L⁆ ≤ D.moduleSubgroup := by
    have hh := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact hh.trans (le_of_eq geometry.full_eq_local)
  exact IsElementaryAbelian.of_injective (inclusion hWV) (inclusion_injective hWV)

/-- The first projection of the original marked pair is precisely the action
on the whole moved module, with no scalar ambiguity. -/
theorem moved_pair_action
    (geometry : ModuleGeometry D) {J V : Type*} [Group J]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : (L ⧸ pCore 2 L) ≃* J) (σ : Representation (ZMod 2) J V)
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (f : localOrbit T L →* J × J)
    (hfirst : ∀ l : L, f ⟨l,le_componentOrbit L T l.property⟩ =
      (e (QuotientGroup.mk' (pCore 2 L) l),1))
    (hsecond : ∀ l : L, f (originalConjugateOrbitInclusion ht l) =
      (1,e (QuotientGroup.mk' (pCore 2 L) l)))
    (r : localOrbit T L) (w : (⁅D.fullModule,L⁆ : Subgroup G)) :
    (d.coordinates ((⁅D.fullModule,L⁆).normalizerMonoidHom
      (inclusion (orbit_normalizes_moved D c) r) w)).toAdd =
      σ (f r).1 (d.coordinates w).toAdd := by
  let := moved_elementary D geometry
  have hgen : L ⊔ L.map (MulAut.conj t).toMonoidHom = localOrbit T L :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn).symm
  apply d.original_action_eq_quotient hgen (orbit_normalizes_moved D c)
    (moved_centralizes_partner D geometry ht htn) ((MonoidHom.fst J J).comp f) σ
  · intro l
    change σ (f ⟨l,_⟩).1 = σ (e (QuotientGroup.mk' (pCore 2 L) l))
    rw [hfirst]
  · rintro ⟨_,l,hl,rfl⟩
    exact congrArg Prod.fst (hsecond ⟨l,hl⟩)

include D c in
/-- In the original marking, inverse conjugation by the chosen Sylow
exchanger turns the second projection into the first. -/
theorem pair_projection_conj_inv_fst
    {J : Type*} [Group J] (e : (L ⧸ pCore 2 L) ≃* J)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (f : localOrbit T L →* J × J)
    (hfirst : ∀ l : L, f ⟨l,le_componentOrbit L T l.property⟩ =
      (e (QuotientGroup.mk' (pCore 2 L) l),1))
    (hsecond : ∀ l : L, f (originalConjugateOrbitInclusion ht l) =
      (1,e (QuotientGroup.mk' (pCore 2 L) l))) (r : localOrbit T L) :
    (f ((localOrbit T L).normalizerMonoidHom
      ⟨t⁻¹,le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem ht)⟩ r)).1 =
        (f r).2 := by
  let R := localOrbit T L
  let K := L.map (MulAut.conj t).toMonoidHom
  let τ := R.normalizerMonoidHom
    ⟨t⁻¹,le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem ht)⟩
  let f₁ := ((MonoidHom.fst J J).comp f).comp τ.toMonoidHom
  let f₂ := (MonoidHom.snd J J).comp f
  have hgen : L ⊔ K = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn).symm
  have htop : L.subgroupOf R ⊔ K.subgroupOf R = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,
      map_subgroupOf_eq_of_le (le_sup_left.trans (le_of_eq hgen)),
      map_subgroupOf_eq_of_le (le_sup_right.trans (le_of_eq hgen)),
      ←MonoidHom.range_eq_map,range_subtype,hgen]
  have hinv : L.map (MulAut.conj t⁻¹).toMonoidHom = K := by
    rcases source_nonnormal_maximal_pair D c.nonnormal ht htn t⁻¹
      (le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem ht)) with he | he
    · have hh := mem_normalizer_iff_map_conj_eq.mpr he
      exact False.elim (htn (by simpa using (normalizer (L : Set G)).inv_mem hh))
    · exact he
  have hK (x : R) (hx : (x : G) ∈ K) : (f x).1 = 1 := by
    obtain ⟨l,hl,he⟩ := hx
    have he' : x = originalConjugateOrbitInclusion ht ⟨l,hl⟩ := Subtype.ext he.symm
    rw [he',hsecond]
  have heq : L.subgroupOf R ⊔ K.subgroupOf R ≤ f₁.eqLocus f₂ := by
    apply sup_le
    · intro l hl
      change (f (τ l)).1 = (f l).2
      rw [hfirst ⟨l,hl⟩]
      apply hK
      rw [←hinv]
      exact mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hl
    · intro x hx
      obtain ⟨l,hl,he⟩ := hx
      have he' : x = originalConjugateOrbitInclusion ht ⟨l,hl⟩ := Subtype.ext he.symm
      change (f (τ x)).1 = (f x).2
      rw [he',hsecond]
      have hτ : τ (originalConjugateOrbitInclusion ht ⟨l,hl⟩) =
          ⟨l,le_componentOrbit L T hl⟩ := by
        apply Subtype.ext
        change t⁻¹*(t*l*t⁻¹)*(t⁻¹)⁻¹ = l
        group
      rw [hτ,hfirst ⟨l,hl⟩]
  exact heq (htop.symm ▸ mem_top r)

include c in
/-- One actual nonidentity Sylow-stabilizer-fixed moved vector is fixed by
all original Hall actors and their inverse-exchanger conjugates. -/
theorem exists_moved_fixed_pair
    (geometry : ModuleGeometry D) {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    {ρ : Representation (ZMod 2) L V}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥ ρ)
    (hzero : ∀ v, (∀ l, ρ l v = v) → v = 0)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ w : (⁅D.fullModule,L⁆ : Subgroup G), d.coordinates w ≠ 1 ∧
      (w : G) ∈ centralizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ∧
      ∀ b : B, Commute (b : G) (w : G) ∧ Commute (b : G) (t*(w : G)*t⁻¹) := by
  let := moved_elementary D geometry
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  obtain ⟨w,hw,hwS⟩ := d.exists_nonidentity_fixed S (stabilizer_normalizes_moved D)
    (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left))
  refine ⟨w,hw,hwS,fun b => ?_⟩
  have hb : Commute (b : G) (w : G) :=
    (hall_centralizes_moved_fixed_of_no_fixed D c geometry d hzero
      (mem_map_of_mem H.subtype b.property) w ⟨w.property,hwS⟩).symm
  have hi : S.relIndex (T : Subgroup G) = 2 := by
    rw [inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal
  have hWV : ⁅D.fullModule,L⁆ ≤ D.moduleSubgroup := by
    have hh := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact hh.trans (le_of_eq geometry.full_eq_local)
  let := D.module_elementary
  have htwV : t*(w : G)*t⁻¹ ∈ D.moduleSubgroup :=
    (mem_normalizer_iff.mp (D.sylow_normalizes_module ht) w).mp (hWV w.property)
  have hc : Commute (w : G) (t*(w : G)*t⁻¹) := congrArg Subtype.val
    (mul_comm (⟨w,hWV w.property⟩ : D.moduleSubgroup) ⟨_,htwV⟩)
  have hz := indexTwo_diagonal_mem_omegaCenter S (T : Subgroup G) inf_le_left hi t ht
    (fun h => htn h.2) w (moved_fixed_mem_omegaCenter D c geometry w.property hwS) hc
  have hHZ : H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact c.central)
  have hdiag : Commute (b : G) ((w : G)*(t*(w : G)*t⁻¹)) :=
    (hHZ b.val.property _ hz).symm
  refine ⟨hb,?_⟩
  change (b : G)*(t*(w : G)*t⁻¹) = (t*(w : G)*t⁻¹)*(b : G)
  apply mul_left_cancel (a := (w : G))
  calc
    (w : G)*((b : G)*(t*(w : G)*t⁻¹)) =
        (b : G)*((w : G)*(t*(w : G)*t⁻¹)) := by
      rw [←mul_assoc,←hb.eq,mul_assoc]
    _ = ((w : G)*(t*(w : G)*t⁻¹))*(b : G) := hdiag.eq
    _ = (w : G)*((t*(w : G)*t⁻¹)*(b : G)) := mul_assoc _ _ _
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
