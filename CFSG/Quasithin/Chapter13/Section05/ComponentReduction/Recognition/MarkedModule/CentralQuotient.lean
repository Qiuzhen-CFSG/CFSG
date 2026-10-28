module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient.Models
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.Sections
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The natural central quotient in 13.5.21(3)

The original action is Action.starRepresentation on U_H/V₁. The marked
irreducible displacement plane forces every proper K*V*-submodule to be
K*-central. Thus its literal fixed-space quotient is chief, and the chief
catalogue identifies that quotient with the actual natural module. Restriction
to K* is irreducible by the concrete model calculations. Every exhaustive
K*-chief flag has exactly one noncentral factor; a finite flag is constructed.
The whole U_H/V₁ may still be a central extension.

The induced H* action is faithful. Its kernel meets simple K* trivially,
hence centralizes K*. Its displacement into C_U(K*) vanishes on [U,K*]=U.
The seed image, original quotient representatives, and tildeEquiv are retained.

This conditional source deduction keeps Recognition.Selected unchanged and
retains the full proper-K input. The configuration and natural-chief catalogue
premises are produced by qt-13-05-recognition-configuration and
qt-13-05-recognition-chief-catalogue; their discharge belongs to the parent
component-analysis/marked-module assembly. No terminal 13.5.23–25 input is used.

Source: Aschbacher–Smith, 13.5.21(3), printed p.924 (PDF p.941), especially
the unique-noncentral-factor paragraph. The direct maximal-submodule argument
is the same moved-plane argument without an assumed composition flag.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient
open Section08.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) (K : Subgroup G)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The actual K*-fixed vectors in the original module U_H/V₁. -/
def centerSpace : Submodule (ZMod 2) (Action.Space D) :=
  fixedSpace (Action.starRepresentation D h) (starImage D.H K)

/-- The literal vector-space quotient by these fixed vectors. -/
abbrev Space := Action.Space D ⧸ centerSpace D h K

/-- The original quotient projection, with precisely the fixed-space kernel. -/
def projection : Action.Space D →ₗ[ZMod 2] Space D h K := (centerSpace D h K).mkQ

/-- The natural quotient retains the image of the marked seed. -/
def seedSpace : Submodule (ZMod 2) (Space D h K) :=
  (Action.seedSpace D).map (projection D h K)

/-- The ambient fixed subrepresentation; its carrier is not enlarged. -/
def centralSubrepresentation (hn : (starImage D.H K).Normal) :
    Subrepresentation (Action.starRepresentation D h) := by
  let := hn
  exact fixedSubrepresentation (Action.starRepresentation D h) (starImage D.H K)

/-- The H* action on the literal central quotient. -/
def representation (hn : (starImage D.H K).Normal) :
    Representation (ZMod 2) (Hstar D.H) (Space D h K) :=
  (centralSubrepresentation D h K hn).quotientRepresentation

/-- Projection intertwines the original and quotient H* actions. -/
theorem representation_mk (hn : (starImage D.H K).Normal) (g : Hstar D.H)
    (w : Action.Space D) :
    representation D h K hn g (projection D h K w) =
      projection D h K (Action.starRepresentation D h g w) := rfl

/-- Precisely the K*-fixed vectors vanish in this quotient. -/
theorem projection_kernel : (projection D h K).ker = centerSpace D h K :=
  Submodule.ker_mkQ _

/-- The projection using the original tilde isomorphism, without a new model map. -/
def tildeProjection (w : D.tilde D.UH) : Space D h K :=
  projection D h K (Additive.ofMul ((Action.tildeEquiv D h).symm w))

/-- The tilde formula agrees with the original U_H/V₁ representative. -/
theorem tildeProjection_apply (w : Action.ModuleGroup D) :
    tildeProjection D h K (Action.tildeEquiv D h w) =
      projection D h K (Additive.ofMul w) := by
  simp only [tildeProjection, MulEquiv.symm_apply_apply]

/-- The fixed space regarded as a subrepresentation of the literal K*V* action. -/
def actorCentral (hn : (starImage D.H K).Normal) :
    Subrepresentation (Catalogue.representation D K h) where
  toSubmodule := centerSpace D h K
  apply_mem_toSubmodule g := (centralSubrepresentation D h K hn).apply_mem_toSubmodule g.val

/-- Restriction to K*V* preserves the exact quotient representation. -/
theorem actorCentral_quotient (hn : (starImage D.H K).Normal) :
    (actorCentral D h K hn).quotientRepresentation =
      (representation D h K hn).comp (Catalogue.actor D K).subtype := rfl

private theorem component_fixedSpace :
    fixedSpace (Catalogue.representation D K h) (Catalogue.component D K) =
      centerSpace D h K := by
  rw [Catalogue.representation, fixedSpace_comp_map, Catalogue.component,
    map_subgroupOf_eq_of_le (show starImage D.H K ≤ Catalogue.actor D K from le_sup_left)]
  rfl

private theorem component_generation
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤) :
    subspaceCommutator (Catalogue.representation D K h) ⊤ (Catalogue.component D K) = ⊤ := by
  apply top_unique
  conv_lhs => rw [← hg]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, w, hw, rfl⟩
  exact Submodule.subset_span
    ⟨⟨k, (show starImage D.H K ≤ Catalogue.actor D K from le_sup_left) hk⟩, hk, w, hw, rfl⟩

private theorem component_noncentral (s : Selected D K) :
    ¬ Catalogue.component D K ≤ (Catalogue.representation D K h).ker := by
  intro hz
  have hk : starImage D.H K = ⊥ := by
    apply bot_unique
    intro k hk
    have he := (Catalogue.representation_injective D K h)
      ((hz (show (⟨k, (show starImage D.H K ≤ Catalogue.actor D K from le_sup_left) hk⟩ : Catalogue.actor D K) ∈ Catalogue.component D K from hk)).trans
        (map_one _).symm)
    exact congrArg Subtype.val he
  exact s.moved (by rw [hk]; simp)

/-- The chief catalogue is used only on genuine irreducible noncentral quotients.
It supplies concrete natural coordinates, not central-quotient chiefness. -/
def ChiefCatalogue : Prop :=
  ∀ N : Subrepresentation (Catalogue.representation D K h), IsCoatom N →
    ¬ Catalogue.component D K ≤ N.quotientRepresentation.ker →
      NaturalAction (Catalogue.component D K) N.quotientRepresentation

/-- The moved-plane argument proves that the actual central quotient is chief. -/
theorem actorCentral_isCoatom (s : Selected D K) (hn : (starImage D.H K).Normal)
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤)
    (v : Catalogue.actor D K)
    (p : MovedPlane (Catalogue.representation D K h) (Catalogue.localActor D K) v)
    (hc : ⁅Catalogue.component D K, zpowers v⁆ = Catalogue.component D K) :
    IsCoatom (actorCentral D h K hn) := by
  let := hn
  let : (Catalogue.component D K).Normal := by
    change ((starImage D.H K).subgroupOf (Catalogue.actor D K)).Normal
    infer_instance
  have he : fixedSubrepresentation (Catalogue.representation D K h)
      (Catalogue.component D K) = actorCentral D h K hn := by
    apply Subrepresentation.toSubmodule_injective
    exact component_fixedSpace D h K
  rw [← he]
  exact p.central_isCoatom _ _ _ _ hc (component_generation D h K hg)
    (component_noncentral D h K s)

private theorem star_noncentral (s : Selected D K) :
    ¬ starImage D.H K ≤ (Action.starRepresentation D h).ker := by
  intro hz
  apply component_noncentral D h K s
  intro k hk
  exact hz hk

/-- Simplicity of K* and whole-module generation imply faithfulness of H* on
this actual quotient, independently of any concrete normalizer calculation. -/
theorem representation_faithful (s : Selected D K)
    (hn : (starImage D.H K).Normal) [IsSimpleGroup (starImage D.H K)]
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤) :
    Function.Injective (representation D h K hn) := by
  let := hn
  let := s.quasisimple
  exact simple_fixedQuotient_faithful (Action.starRepresentation D h) (starImage D.H K)
    (Action.starRepresentation_injective D h) (star_noncentral D h K s) hg

/-- Noncentrality survives on the quotient, retaining its literal representatives. -/
theorem actorCentral_noncentral (s : Selected D K) (hn : (starImage D.H K).Normal) :
    ¬ Catalogue.component D K ≤ (actorCentral D h K hn).quotientRepresentation.ker := by
  intro hz
  let := hn
  let := s.quasisimple
  apply fixedQuotient_noncentral (Action.starRepresentation D h) (starImage D.H K)
    (star_noncentral D h K s)
  intro k hk
  apply (quotient_kernel_iff (Action.starRepresentation D h) (starImage D.H K) k).mpr
  intro w
  have hk' : (⟨k, (show starImage D.H K ≤ Catalogue.actor D K from le_sup_left) hk⟩ :
      Catalogue.actor D K) ∈ Catalogue.component D K := hk
  have he := LinearMap.congr_fun (hz hk') ((centerSpace D h K).mkQ w)
  exact (Submodule.Quotient.eq (centerSpace D h K)).mp he

/-- The chief catalogue now applies to a proved chief quotient. -/
theorem natural_quotient (s : Selected D K) (hn : (starImage D.H K).Normal)
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤)
    (v : Catalogue.actor D K)
    (p : MovedPlane (Catalogue.representation D K h) (Catalogue.localActor D K) v)
    (hc : ⁅Catalogue.component D K, zpowers v⁆ = Catalogue.component D K)
    (catalogue : ChiefCatalogue D h K) :
    NaturalAction (Catalogue.component D K)
      ((representation D h K hn).comp (Catalogue.actor D K).subtype) := by
  rw [← actorCentral_quotient D h K hn]
  exact catalogue (actorCentral D h K hn) (actorCentral_isCoatom D h K s hn hg v p hc)
    (actorCentral_noncentral D h K s hn)

/-- The actual K* action on the original module. -/
def componentRepresentation : Representation (ZMod 2) (starImage D.H K) (Action.Space D) :=
  (Action.starRepresentation D h).comp (starImage D.H K).subtype

/-- Restriction of the same fixed subspace to the component action. -/
def componentCentral (hn : (starImage D.H K).Normal) :
    Subrepresentation (componentRepresentation D h K) where
  toSubmodule := centerSpace D h K
  apply_mem_toSubmodule g := (centralSubrepresentation D h K hn).apply_mem_toSubmodule g.val

/-- The natural coordinates give irreducibility on K* itself. -/
theorem component_quotient_irreducible (hn : (starImage D.H K).Normal)
    (hnatural : NaturalAction (Catalogue.component D K)
      ((representation D h K hn).comp (Catalogue.actor D K).subtype)) :
    IsIrreducible (componentCentral D h K hn).quotientRepresentation := by
  let e := (subgroupOfEquivOfLe
    (show starImage D.H K ≤ Catalogue.actor D K from le_sup_left)).symm
  exact irreducible_of_surjective_equivariant _ _ e.toMonoidHom e.surjective
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) hnatural.component_irreducible

private theorem component_top_generation
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤) :
    subspaceCommutator (componentRepresentation D h K) ⊤ ⊤ = ⊤ := by
  apply top_unique
  conv_lhs => rw [← hg]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, w, hw, rfl⟩
  exact Submodule.subset_span ⟨⟨k, hk⟩, mem_top _, w, hw, rfl⟩

private theorem component_central_fixed (hn : (starImage D.H K).Normal) :
    (componentCentral D h K hn).toSubmodule ≤
      fixedSpace (componentRepresentation D h K) ⊤ := by
  intro w hw k
  exact hw k.val

/-- Every proper K*-invariant subspace of the original module is centralized. -/
theorem component_submodule_central (hn : (starImage D.H K).Normal)
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤)
    (hnatural : NaturalAction (Catalogue.component D K)
      ((representation D h K hn).comp (Catalogue.actor D K).subtype))
    (N : Subrepresentation (componentRepresentation D h K)) :
    N = ⊤ ∨ N.toSubmodule ≤ fixedSpace (componentRepresentation D h K) ⊤ := by
  let := component_quotient_irreducible D h K hn hnatural
  exact eq_top_or_central_of_irreducible_central_quotient _ ⊤
    (componentCentral D h K hn) (component_central_fixed D h K hn)
    (component_top_generation D h K hg) N

/-- Every exhaustive chief flag for K* has exactly one noncentral factor. -/
theorem unique_noncentral_factor (s : Selected D K) (hn : (starImage D.H K).Normal)
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤)
    (hnatural : NaturalAction (Catalogue.component D K)
      ((representation D h K hn).comp (Catalogue.actor D K).subtype))
    (c : ℕ → Subrepresentation (componentRepresentation D h K)) (n : ℕ)
    (hzero : c 0 = ⊥) (hstop : c n = ⊤) (hchief : ∀ i < n, c i ⋖ c (i + 1)) :
    ∃! i, i < n ∧ ¬ (⊤ : Subgroup (starImage D.H K)) ≤
      (sectionRepresentation (componentRepresentation D h K) (c i) (c (i + 1))).ker := by
  apply unique_noncentral_in_flag _ ⊤ (component_top_generation D h K hg) _
    (component_submodule_central D h K hn hg hnatural) c n hzero hstop hchief
  intro hz
  apply star_noncentral D h K s
  intro k hk
  exact hz (mem_top (⟨k, hk⟩ : starImage D.H K))

/-- Existence is proved, including exhaustive endpoints and genuine chief steps. -/
theorem exists_unique_noncentral_chief_flag (s : Selected D K)
    (hn : (starImage D.H K).Normal)
    (hg : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤)
    (hnatural : NaturalAction (Catalogue.component D K)
      ((representation D h K hn).comp (Catalogue.actor D K).subtype)) :
    ∃ (c : ℕ → Subrepresentation (componentRepresentation D h K)) (n : ℕ),
      Monotone c ∧ c 0 = ⊥ ∧ c n = ⊤ ∧ (∀ i < n, c i ⋖ c (i + 1)) ∧
      ∃! i, i < n ∧ ¬ (⊤ : Subgroup (starImage D.H K)) ≤
        (sectionRepresentation (componentRepresentation D h K) (c i) (c (i + 1))).ker := by
  obtain ⟨c, n, hc, hzero, hstop, hchief⟩ := exists_chief_flag (componentRepresentation D h K)
  exact ⟨c, n, hc, hzero, hstop, hchief,
    unique_noncentral_factor D h K s hn hg hnatural c n hzero hstop hchief⟩

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
/-- The source point is centralized by K, so every chief factor below V₁ is central. -/
theorem point_prefix_central (s : Selected D K) (A B : Subgroup G) (hB : B ≤ D.V₁) :
    ⁅B, K⁆ ≤ A := by
  have he : ⁅K, B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((s.le_H.trans h.H_centralizes).trans (centralizer_le hB))
  rw [commutator_comm, he]
  exact bot_le

/-- The quotient action is still conjugation on the original representatives. -/
theorem representation_representative (hn : (starImage D.H K).Normal)
    (x : D.H) (u : D.UH) :
    representation D h K hn (QuotientGroup.mk' (pCore 2 D.H) x)
      (projection D h K (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u))) =
    projection D h K (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
      ⟨x.val * u.val * x.val⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
          x.val x.property u.val u.property⟩)) := by
  rw [representation_mk, Action.starRepresentation_apply]

/-- The actual seed-to-central-quotient map. -/
def seedMap : Action.seedSpace D →ₗ[ZMod 2] Space D h K :=
  (projection D h K).comp (Action.seedSpace D).subtype

/-- The marked plane embeds in the central quotient, even when the whole module does not. -/
theorem seedMap_injective (s : Selected D K) (hn : (starImage D.H K).Normal)
    (v : Catalogue.actor D K)
    (p : MovedPlane (Catalogue.representation D K h) (Catalogue.localActor D K) v)
    (hseed : p.plane.toSubmodule = Action.seedSpace D)
    (hc : ⁅Catalogue.component D K, zpowers v⁆ = Catalogue.component D K) :
    Function.Injective (seedMap D h K) := by
  have hz := actorCentral_noncentral D h K s hn
  have hi := p.quotientMap_injective _ _ _ _ hc (actorCentral D h K hn) hz
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hx' : ((actorCentral D h K hn).toSubmodule.mkQ.comp p.plane.toSubmodule.subtype)
      ⟨x, hseed.symm ▸ x.property⟩ = 0 := hx
  have he := hi (hx'.trans (map_zero _).symm)
  exact Subtype.ext (congrArg (fun z : p.plane.toSubmodule => (z : Action.Space D)) he)

/-- The marked quotient plane still has dimension two. -/
theorem seedSpace_finrank (s : Selected D K) (hn : (starImage D.H K).Normal)
    (v : Catalogue.actor D K)
    (p : MovedPlane (Catalogue.representation D K h) (Catalogue.localActor D K) v)
    (hseed : p.plane.toSubmodule = Action.seedSpace D)
    (hc : ⁅Catalogue.component D K, zpowers v⁆ = Catalogue.component D K) :
    Module.finrank (ZMod 2) (seedSpace D h K) = 2 := by
  have he := (LinearEquiv.ofInjective (seedMap D h K)
    (seedMap_injective D h K s hn v p hseed hc)).finrank_eq
  have hr : (seedMap D h K).range = seedSpace D h K := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hr] at he
  rw [← he, ← hseed]
  exact p.dimension

/-- In the quotient the same marked plane is precisely the distinguished displacement. -/
theorem seedSpace_eq_moved (hn : (starImage D.H K).Normal)
    (v : Catalogue.actor D K)
    (p : MovedPlane (Catalogue.representation D K h) (Catalogue.localActor D K) v)
    (hseed : p.plane.toSubmodule = Action.seedSpace D) :
    seedSpace D h K = LinearMap.range (representation D h K hn v.val - 1) := by
  have hp : Action.seedSpace D = LinearMap.range (Action.starRepresentation D h v.val - 1) :=
    hseed.symm.trans p.moved
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, rfl⟩ := (hp ▸ hx)
    refine ⟨projection D h K w, ?_⟩
    change representation D h K hn v.val (projection D h K w) - projection D h K w = _
    rw [representation_mk, ← map_sub]
    rfl
  · rintro ⟨q, rfl⟩
    obtain ⟨w, rfl⟩ := (centerSpace D h K).mkQ_surjective q
    refine ⟨Action.starRepresentation D h v.val w - w, hp.symm ▸ ⟨w, rfl⟩, ?_⟩
    change projection D h K (_ - _) =
      representation D h K hn v.val (projection D h K w) - projection D h K w
    rw [representation_mk, map_sub]


/-- Application to the source setup and original selected component. The
configuration and chief catalogue remain precisely the independent inputs. -/
theorem source_central_quotient (s : Selected D K)
    (_properK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H)) (hLK : D.L₁ ≤ K)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    [IsSimpleGroup (starImage D.H K)]
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : Catalogue.actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (p : MovedPlane (Catalogue.representation D K h) (Catalogue.localActor D K) v)
    (seed_marking : p.plane.toSubmodule = Action.seedSpace D)
    (catalogue : ChiefCatalogue D h K) :
    ∃ hn : (starImage D.H K).Normal,
      D.tilde D.UH = ⁅D.tilde D.UH, D.tilde K⁆ ∧
      subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤ ∧
      NaturalAction (Catalogue.component D K)
        ((representation D h K hn).comp (Catalogue.actor D K).subtype) ∧
      Function.Injective (representation D h K hn) ∧
      Function.Injective (seedMap D h K) ∧
      Module.finrank (ZMod 2) (seedSpace D h K) = 2 ∧
      seedSpace D h K = LinearMap.range (representation D h K hn v.val - 1) ∧
      ∃ (c : ℕ → Subrepresentation (componentRepresentation D h K)) (n : ℕ),
        Monotone c ∧ c 0 = ⊥ ∧ c n = ⊤ ∧ (∀ i < n, c i ⋖ c (i + 1)) ∧
        ∃! i, i < n ∧ ¬ (⊤ : Subgroup (starImage D.H K)) ≤
          (sectionRepresentation (componentRepresentation D h K) (c i) (c (i + 1))).ker := by
  have hnK := normal_in_H s h hSQ hLK hm
  have hn : (starImage D.H K).Normal :=
    Subgroup.Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  have hg := linear_generation D h s hLK hnK hseed
  have hc := Catalogue.component_commutator D K h s hcard heven v hv
  have hnat := natural_quotient D h K s hn hg v p hc catalogue
  exact ⟨hn, tilde_generation s h hLK hnK hseed, hg, hnat,
    representation_faithful D h K s hn hg,
    seedMap_injective D h K s hn v p seed_marking hc,
    seedSpace_finrank D h K s hn v p seed_marking hc,
    seedSpace_eq_moved D h K hn v p seed_marking,
    exists_unique_noncentral_chief_flag D h K s hn hg hnat⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient
