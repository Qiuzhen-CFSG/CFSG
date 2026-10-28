module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusDisplacement

/-!
# The escaped terminal displacement has an actual escaping conjugate

Under the small radius budget, the full kernel N = V_a ∩ Q_z escapes the
penultimate Q_e. Its displacement H = [Z_e,N] is noncentral at e while
lying in Z_z. If every local conjugate of H remained in Z_z, the normal
join of those conjugates would be fixed by N and Q_e. Simplicity of the
same marked vertex quotient then makes this join central at e, a
contradiction. Thus a literal residual conjugate escapes the original Z_z.

The entire kernel and every fixed central attachment are retained. This
is a further constraint on the open small-budget branch of MS93 (5.11),
printed p.923; it does not supply the missing strict q-squared bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem conjugate_escape_from_fixed_seed
    {G J : Type*} [Group G] [Group J] [IsSimpleGroup J]
    (S Q Z A D E : Subgroup G) (f : S →* J) (hf : Function.Surjective f)
    (hk : f.ker.map S.subtype = Q)
    (hZS : Z ≤ S) (hZn : S ≤ normalizer (Z : Set G))
    (hZQ : Z ≤ centralizer (Q : Set G))
    (hAS : A ≤ S) (hAQ : ¬ A ≤ Q) (hDZ : D ≤ Z)
    (hEA : E ≤ centralizer (A : Set G))
    (hD : ¬ D ≤ centralizer (S : Set G)) :
    ∃ g ∈ S, ∃ x ∈ D, g*x*g⁻¹ ∉ E := by
  classical
  by_contra! hno
  let W := conjugateSpanBy D S
  have hWZ : W ≤ Z := conjugateSpanBy_le hDZ hZn
  have hWS : W ≤ S := hWZ.trans hZS
  have hWE : W ≤ E := by
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,x,hx,rfl⟩
    exact hno g hg x hx
  let W₀ := W.subgroupOf S
  let C := centralizer (W₀ : Set S)
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy D S)
  let : C.Normal := inferInstance
  have hker : f.ker ≤ C := by
    intro k hk₀ w hw
    apply Subtype.val_injective
    have hkQ : k.val∈Q := hk ▸ mem_map_of_mem S.subtype hk₀
    exact (hZQ (hWZ hw) k.val hkQ).symm
  have hAC : A.subgroupOf S ≤ C := by
    intro x hx w hw
    apply Subtype.val_injective
    exact (hEA (hWE hw) x.val hx).symm
  have hnker : ¬ C ≤ f.ker := by
    intro hCk
    apply hAQ
    intro x hx
    exact hk ▸ mem_map_of_mem S.subtype
      (hCk (hAC (show (⟨x,hAS hx⟩ : S) ∈ A.subgroupOf S from hx)))
  have hmap : C.map f=⊤ := by
    rcases (Normal.map (inferInstance : C.Normal) f hf).eq_bot_or_eq_top with hz | ht
    · exact False.elim (hnker ((map_eq_bot_iff C).mp hz))
    · exact ht
  have hCtop : C=⊤ := by
    have hh := congrArg (Subgroup.comap f) hmap
    simpa only [comap_map_eq,comap_top,sup_eq_left.mpr hker] using hh
  apply hD
  intro x hx y hy
  have hxy : (⟨y,hy⟩ : S) ∈ C := hCtop ▸ mem_top _
  exact (congrArg Subtype.val (hxy (⟨x,hWS (le_conjugateSpanBy D S hx)⟩ : S)
    (le_conjugateSpanBy D S hx))).symm

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual terminal displacement has a local conjugate outside the
original opposite seed. The actor is the full original endpoint kernel. -/
theorem Input.replacement_small_radius_terminal_displacement_conjugate_escape
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    let e := path.walk.getVert (geometry.b d.radical-2)
    let N := V d.radical a ⊓ Q d.radical z
    ∃ g ∈ Ltilde d.radical e, ∃ x ∈ ⁅Z d.radical e,N⁆,
      g*x*g⁻¹ ∉ Z d.radical z := by
  dsimp only
  let e := path.walk.getVert (geometry.b d.radical-2)
  let N := V d.radical a ⊓ Q d.radical z
  have hecol : color d.radical e=false := by
    apply (path.vertex_color (by rw [path.length_eq_b]; omega)).mpr
    have heven : Even (geometry.b d.radical) := geometry.even (alpha d.radical) rfl
    rw [Nat.even_iff] at heven ⊢
    omega
  have hdist : (cosetGraph d.radical).dist a e=geometry.b d.radical-2 :=
    path.dist_start (by rw [path.length_eq_b]; omega)
  have hNS : N ≤ stabilizer d.radical e := inf_le_left.trans
    (Sp4Four.radius_le_stabilizer_of_distance d.radical geometry path.start_color
      (by rw [hdist]; omega))
  have hescape := h.replacement_small_radius_penultimate_kernel_escape d path hb hi
  obtain ⟨E,hE,f,hf,hfQ,_⟩ :=
    h.replacement_inner_natural_action d geometry hb.le hecol
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hplace := (h.replacement_small_radius_terminal_kernel_movement d path hb hi).2.2
  have hZQ : Z d.radical e ≤ centralizer (Q d.radical e : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes e hecol)
  have hzN : Z d.radical z ≤ centralizer (N : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)).trans
      (centralizer_le inf_le_right)
  obtain ⟨g,hg,x,hx,hout⟩ := conjugate_escape_from_fixed_seed (stabilizer d.radical e) (Q d.radical e)
    (Z d.radical e) N ⁅Z d.radical e,N⁆ (Z d.radical z) f hf hfQ
    (Z_le_stabilizer _ _) (Z_normalized _ _) hZQ hNS hescape
    (hplace.trans (inf_le_left.trans inf_le_right)) hzN
    (h.replacement_small_radius_terminal_displacement_not_central d path hb hi)
  obtain ⟨i,_,hir,hiL,_,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
    d.radical (h.replacement_two_group d) (h.replacement_core_le d) hecol
  have hS : Ltilde d.radical e ⊔ Q d.radical e=stabilizer d.radical e := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb.le,←MonoidHom.range_eq_map,hir]
  have hgprod : g ∈ (Ltilde d.radical e : Set (FreeAmalgam d.radical))*
      (Q d.radical e : Set _) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _
      ((Ltilde_le_stabilizer e).trans (Q_normalized d.radical e)),hS]
    exact hg
  obtain ⟨l,hl,q,hq,rfl⟩ := hgprod
  refine ⟨l,hl,x,hx,?_⟩
  have hqx : q*x*q⁻¹=x := mul_inv_eq_iff_eq_mul.mpr
    (hZQ ((hplace hx).1.2) q hq)
  have heq : (l*q)*x*(l*q)⁻¹=l*x*l⁻¹ := by
    calc
      (l*q)*x*(l*q)⁻¹=l*(q*x*q⁻¹)*l⁻¹ := by group
      _=l*x*l⁻¹ := by rw [hqx]
  exact heq ▸ hout

/-- The surviving displacement cannot be normal at the penultimate vertex. -/
theorem Input.replacement_small_radius_terminal_displacement_not_normal
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    let e := path.walk.getVert (geometry.b d.radical-2)
    ¬ stabilizer d.radical e ≤ normalizer
      ((⁅Z d.radical e,V d.radical a ⊓ Q d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  dsimp only
  intro hn
  obtain ⟨g,hg,x,hx,hout⟩ :=
    h.replacement_small_radius_terminal_displacement_conjugate_escape d path hb hi
  have hplace := (h.replacement_small_radius_terminal_kernel_movement d path hb hi).2.2
  exact hout (hplace (le_normalizer_iff.mp hn g (Ltilde_le_stabilizer _ hg) x hx)).2

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
