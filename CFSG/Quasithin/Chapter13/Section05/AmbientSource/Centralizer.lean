module
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Plane
public import CFSG.Quasithin.Chapter13.Section03.LocalSteps
public import CFSG.Quasithin.Chapter13.Section05.PointAction

/-!
# The ambient centralizer and its literal point-action consumer

Once the source point-core moves V₂, the plane normal closure makes the
original cubic parabolic normal in N_G(V₂). Parabolic conjugate generation
then puts C_G(V₃) in N_G(L); the genuine 12.2.6 TI property puts it in N_G(V).
This supplies exactly the earlier centralizer input to the checked natural
point-fixer theorem and hence the original 13.5.5 normalizer intersection.

The source implications 13.3.14, 12.2.6 and parabolic generation are explicit
remaining inputs. They are not consequences asserted from NaturalSetup.
Source: Aschbacher–Smith, 13.3.15(6), p.894; 13.5.4(4) and 13.5.5, p.916.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsKleinFour
namespace CFSG.Quasithin.Chapter13.Section05.AmbientSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

/-- The literal source plane is a four-group. -/
theorem source_plane_isKleinFour {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H) : IsKleinFour E := by
  let := d.chosen.elementary
  let := IsElementaryAbelian.of_le (p := 2) (d.plane_le_seed.trans d.seed_le)
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.plane_card]; decide)
  exact ⟨d.plane_card,IsElementaryAbelian.exponent_eq_prime⟩

omit [Finite G] in
private theorem parabolic_generation_form (L X U : Subgroup G)
    (hgen : L = conjugateSpanBy X (L ⊓ normalizer (U : Set G))) :
    L = closure {x : G | ∃ l : (L ⊓ normalizer (U : Set G) : Subgroup G),
      ∃ v : X, x = (l : G) * (v : G) * (l : G)⁻¹} := by
  apply hgen.trans
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨l,hl,v,hv,he⟩
    exact ⟨⟨l,hl⟩,⟨v,hv⟩,he.symm⟩
  · rintro ⟨l,v,he⟩
    exact ⟨l.val,l.property,v.val,v.property,he.symm⟩

omit [Finite G] in
/-- The ambient part of 13.3.15(6), retaining both M and N_G(V). -/
theorem centralizer_le_MV_of_parabolic_normality
    (V U L X M : Subgroup G)
    (hX : centralizer (U : Set G) ≤ normalizer (X : Set G))
    (hgen : L = conjugateSpanBy X (L ⊓ normalizer (U : Set G)))
    (hM : M = normalizer (L : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hU : U ≠ ⊥) (hUV : U ≤ V) :
    centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G) := by
  have hg := parabolic_generation_form L X U hgen
  have hNC : normalizer (U : Set G) ≤
      normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hperm : ((centralizer (U : Set G)) : Set G) *
      ((L ⊓ normalizer (U : Set G)) : Set G) =
      ((L ⊓ normalizer (U : Set G)) : Set G) *
        ((centralizer (U : Set G)) : Set G) :=
    (set_mul_normalizer_comm _ _ (inf_le_right.trans hNC)).symm
  apply le_inf
  · rw [hM,hg]
    exact le_normalizer_conjugate_closure_of_mul_subset _ _ _ hX hperm.le
  · exact Section03.centralizer_le_normalizer_of_parabolic_generation V U L X
      hX hg hTI hU hUV

/-- The original natural configuration consumes the plane-normal-closure
argument. The preceding 13.3.14 noncentrality, 13.2 parabolic generation,
and 12.2.6 TI property are stated explicitly until their source producers
are assembled; no ambient conclusion is an input. -/
theorem source_centralizer_of_noncentrality
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H) (X : Subgroup G)
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : letI := source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G))
    (hm : ⁅(normalizer (P : Set G)).pCoreIn 2, E⁆ ≠ ⊥)
    (hgen : L = conjugateSpanBy X (L ⊓ normalizer (U : Set G)))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) :
    centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G) := by
  let := source_plane_isKleinFour d
  have hn := (plane_normalClosure T P E X d.line_card d.line_le_plane
    d.line_stable d.plane_stable hXN hTX hX hx hkX hm).2.1
  apply centralizer_le_MV_of_parabolic_normality V U L X M
    ((centralizer_le d.plane_le_seed).trans ((Subgroup.centralizer_le_normalizer _).trans hn))
    hgen d.local_normalizer hTI ?_ d.seed_le
  intro he
  have hc := d.seed_card
  simp [he] at hc

/-- Literal 13.5.5 consumer, with the complete natural point-fixer action
already constructed by PointAction.source_action. -/
theorem source_normalizer_intersection_of_noncentrality
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H) (X : Subgroup G)
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : letI := source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G))
    (hm : ⁅(normalizer (P : Set G)).pCoreIn 2, E⁆ ≠ ⊥)
    (hgen : L = conjugateSpanBy X (L ⊓ normalizer (U : Set G)))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) :
    H ⊓ normalizer (U : Set G) ≤ M ⊓ normalizer (V : Set G) :=
  PointAction.normalizer_intersection_source d
    (source_centralizer_of_noncentrality d X hXN hTX hX hx hkX hm hgen hTI)

end CFSG.Quasithin.Chapter13.Section05.AmbientSource
