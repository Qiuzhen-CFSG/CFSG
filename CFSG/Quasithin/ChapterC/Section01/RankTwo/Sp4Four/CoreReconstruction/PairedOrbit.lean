module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreRecognition.SecondaryOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.Frattini.FiniteConjugateSpan

/-!
# Maximal secondary seeds and their paired Frattini bound

The source's maximal subgroup is the greatest commutator preimage in the
opposite Z-layer. Positive critical distance makes that layer elementary,
so it normalizes the common edge layer and the construction has the required
universal property. The actual two-kernel normalizes the seed.

For the two literal conjugate orbits, local kernel containment supplies
finiteness, two-group structure and mutual normalization. Seed commutator
bounds with trivial intersection then give disjoint ambient Frattini groups.
The final theorem feeds these conclusions to the proved involution-orbit
argument, retaining the source natural section and its central kernel.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public section
open Subgroup Representation
open scoped commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {G : Type*} [Group G]

theorem conjugatesIn_eq_conjugateSpan (Y H : Subgroup G) :
    conjugatesIn Y H = conjugateSpanBy Y H := by
  rw [conjugateSpanBy_eq_iSup_conj]
  apply le_antisymm
  · apply iSup_le
    intro h
    exact le_iSup_of_le (h⁻¹ : H) le_rfl
  · apply iSup_le
    intro h
    apply le_iSup_of_le (h⁻¹ : H)
    simp only [rightConjugate, inv_inv, coe_inv]
    exact le_rfl

theorem conjugatesIn_le_of_normalized (Y H P : Subgroup G)
    (hYP : Y ≤ P) (hHP : H ≤ normalizer P) : conjugatesIn Y H ≤ P := by
  rw [conjugatesIn_eq_conjugateSpan]
  exact conjugateSpanBy_le hYP hHP

theorem conjugatesIn_frattini_le (Y H P : Subgroup G)
    [Finite (conjugatesIn Y H)] [IsElementaryAbelian 2 Y]
    (hp : IsPGroup 2 P) (hYP : Y ≤ P) (hHP : H ≤ normalizer P) :
    (frattini (conjugatesIn Y H)).map (conjugatesIn Y H).subtype ≤
      ⁅conjugatesIn Y H,P⁆ := by
  have hle := conjugatesIn_le_of_normalized Y H P hYP hHP
  have htwo := hp.of_injective (inclusion hle) (inclusion_injective _)
  have hc : ⁅conjugatesIn Y H,conjugatesIn Y H⁆ ≤ ⁅conjugatesIn Y H,P⁆ :=
    commutator_mono le_rfl hle
  rw [conjugatesIn_eq_conjugateSpan] at htwo hc ⊢
  have he := conjugatesIn_eq_conjugateSpan Y H
  let : Finite (conjugateSpanBy Y H) := he ▸ inferInstance
  exact finite_conjugateSpan_frattini_le Y H _ htwo hc

variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

/-- The greatest source seed Y at the opposite endpoint. -/
noncomputable def secondarySeed (a t a' : Vertex R) : Subgroup (FreeAmalgam R) :=
  commutatorPreimage (Z R a') (Q R a) (Z R t)

omit [Finite M] in
theorem secondarySeed_le (a t a' : Vertex R) : secondarySeed R a t a' ≤ Z R a' :=
  commutatorPreimage_le _ _ _

omit [Finite M] in
theorem edge_Z_le_endpoint {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : Z R t ≤ Z R a := by
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    cases hc : color R t <;> simp_all
  simp only [Z,ha,ht,↓reduceIte]
  exact le_iSup_of_le t (le_iSup_of_le hat le_rfl)

omit [Finite M] in
theorem secondarySeed_greatest (geometry : Geometry R) {a t a' : Vertex R}
    (ha' : color R a' = false) (ha't : Adjacent R a' t)
    (hb : 0 < geometry.b R) :
    secondarySeed R a t a' ≤ Z R a' ∧
      ⁅secondarySeed R a t a',Q R a⁆ ≤ Z R t ∧
      ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Z R a' → ⁅Y,Q R a⁆ ≤ Z R t →
        Y ≤ secondarySeed R a t a' := by
  have hba' : 0 < criticalDistance R a' (geometry.exists_critical a' ha') := by
    rw [geometry.distance_constant a' ha']
    exact hb
  let := Z_elementary_of_positive R geometry a' ha' hba'
  have hn : Z R a' ≤ normalizer (Z R t) := by
    apply le_centralizer_iff.mp ?_ |>.trans (Subgroup.centralizer_le_normalizer _)
    intro z hz y hy
    have hcomm := (IsMulCommutative.is_comm (M := Z R a')).comm
      ⟨y,hy⟩ ⟨z,edge_Z_le_endpoint R ha' ha't hz⟩
    exact congrArg Subtype.val hcomm
  exact ⟨secondarySeed_le R a t a',
    commutator_commutatorPreimage_le _ _ _ hn,
    fun _ hY hc => le_commutatorPreimage hY hc⟩
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

theorem secondary_orbit_frattini_le (geometry : Geometry R)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {a a' : Vertex R} (ha : color R a = false) (ha' : color R a' = false)
    (hb : 0 < geometry.b R) (Y : Subgroup (FreeAmalgam R))
    (hY : Y ≤ Z R a') (hYQ : Y ≤ Q R a) :
    (frattini (secondaryOrbit R a Y)).map (secondaryOrbit R a Y).subtype ≤
      ⁅secondaryOrbit R a Y,Q R a⁆ := by
  let := finite_stabilizer R a
  have hYA : Y ≤ stabilizer R a := hYQ.trans (fun _ hx => hx.1)
  let : Finite (conjugatesIn Y (stabilizer R a)) :=
    Finite.of_injective (inclusion (conjugatesIn_le Y _ hYA)) (inclusion_injective _)
  have hba' : 0 < criticalDistance R a' (geometry.exists_critical a' ha') := by
    rw [geometry.distance_constant a' ha']; exact hb
  let := Z_elementary_of_positive R geometry a' ha' hba'
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective (inclusion hY) (inclusion_injective _)
  exact conjugatesIn_frattini_le Y (stabilizer R a) (Q R a)
    (Q_isPGroup R hp hQR a ha) hYQ (Q_normalized R a)

theorem secondary_orbits_frattini_disjoint (geometry : Geometry R)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {a a' : Vertex R} (ha : color R a = false) (ha' : color R a' = false)
    (hb : 0 < geometry.b R) (Y X : Subgroup (FreeAmalgam R))
    (hY : Y ≤ Z R a') (hX : X ≤ Z R a)
    (hYQ : Y ≤ Q R a) (hXQ : X ≤ Q R a')
    (hcomm : ⁅secondaryOrbit R a Y,Q R a⁆ ≤ ⁅Y,Q R a⁆)
    (hcomm' : ⁅secondaryOrbit R a' X,Q R a'⁆ ≤ ⁅X,Q R a'⁆)
    (hdis : Disjoint ⁅Y,Q R a⁆ ⁅X,Q R a'⁆) :
    Disjoint ((frattini (secondaryOrbit R a Y)).map (secondaryOrbit R a Y).subtype)
      ((frattini (secondaryOrbit R a' X)).map (secondaryOrbit R a' X).subtype) :=
  hdis.mono
    ((secondary_orbit_frattini_le R geometry hp hQR ha ha' hb Y hY hYQ).trans hcomm)
    ((secondary_orbit_frattini_le R geometry hp hQR ha' ha hb X hX hXQ).trans hcomm')

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M F : Type*} [Group M] [Finite M] [Field F] [Algebra (ZMod 2) F]

theorem secondary_orbit_centralizes_of_paired_seed_commutators
    (R : Subgroup M) (geometry : Geometry R)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {a a' : Vertex R} (ha : color R a = false) (ha' : color R a' = false)
    (hb : 0 < geometry.b R) (hd : (cosetGraph R).dist a a' = 2)
    (Y X D : Subgroup (FreeAmalgam R))
    (hY : Y ≤ Z R a') (hX : X ≤ Z R a)
    (hYQ : Y ≤ Q R a) (hXQ : X ≤ Q R a')
    (q : stabilizer R a →* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hq : Function.Surjective q)
    (d : BinaryConjugationSection (stabilizer R a) (secondaryOrbit R a Y) D
      ((restrictScalars (k := ZMod 2) (symplecticNatural 2)).comp q))
    (hcomm : ⁅secondaryOrbit R a Y,Q R a⁆ ≤ ⁅Y,Q R a⁆)
    (hcomm' : ⁅secondaryOrbit R a' X,Q R a'⁆ ≤ ⁅X,Q R a'⁆)
    (hdis : Disjoint ⁅Y,Q R a⁆ ⁅X,Q R a'⁆)
    (hD : D ≤ ⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ ⊔ Z R a)
    (hcentral : D ≤ centralizer (secondaryOrbit R a Y : Set (FreeAmalgam R))) :
    ⁅secondaryOrbit R a Y,Y⁆ = ⊥ := by
  have hAQ : secondaryOrbit R a Y ≤ Q R a :=
    conjugatesIn_le_of_normalized Y _ _ hYQ (Q_normalized R a)
  have hA'Q : secondaryOrbit R a' X ≤ Q R a' :=
    conjugatesIn_le_of_normalized X _ _ hXQ (Q_normalized R a')
  have hAQ' : secondaryOrbit R a Y ≤ stabilizer R a' :=
    hAQ.trans (Q_le_stabilizer_of_dist_two R a a' ha hd)
  have hA'Q' : secondaryOrbit R a' X ≤ stabilizer R a :=
    hA'Q.trans (Q_le_stabilizer_of_dist_two R a' a ha' (by rwa [SimpleGraph.dist_comm]))
  have hcross : ⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ ≤ secondaryOrbit R a Y :=
    le_normalizer_iff_commutator_le_left.mp
      (hA'Q'.trans (conjugatesIn_normalized Y _))
  have hcross' : ⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ ≤ secondaryOrbit R a' X :=
    le_normalizer_iff_commutator_le_right.mp
      (hAQ'.trans (conjugatesIn_normalized X _))
  have hphi := secondary_orbits_frattini_disjoint R geometry hp hQR ha ha' hb Y X
    hY hX hYQ hXQ hcomm hcomm' hdis
  have hZ : Z R a ≤ centralizer (secondaryOrbit R a Y : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)).trans
      (centralizer_le hAQ)
  exact secondary_orbit_centralizes_seed R geometry a a' ha ha' hb Y X D hY
    (hXQ.trans (fun _ hx => hx.1)) q hq d
    ((Q_isPGroup R hp hQR a ha).of_injective (inclusion hAQ) (inclusion_injective _))
    ((Q_isPGroup R hp hQR a' ha').of_injective (inclusion hA'Q) (inclusion_injective _))
    hcross hcross' hphi hD hZ hcentral

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

omit [Finite M] in
theorem secondarySeed_elementary (geometry : Geometry R) {a t a' : Vertex R}
    (ha' : color R a' = false) (hb : 0 < geometry.b R) :
    IsElementaryAbelian 2 (secondarySeed R a t a') := by
  let := Z_elementary_of_positive R geometry a' ha'
    (lt_of_lt_of_eq hb (geometry.distance_constant a' ha').symm)
  exact IsElementaryAbelian.of_injective (inclusion (secondarySeed_le R a t a'))
    (inclusion_injective _)

theorem secondarySeed_normalized_by_kernel (geometry : Geometry R)
    {a t a' : Vertex R} (ha : color R a = false) (ha' : color R a' = false)
    (hat : Adjacent R a t) (ha't : Adjacent R a' t)
    (hb : 0 < geometry.b R) (hd : (cosetGraph R).dist a a' = 2) :
    Q R a ≤ normalizer (secondarySeed R a t a') := by
  let := Z_elementary_of_positive R geometry a' ha'
    (lt_of_lt_of_eq hb (geometry.distance_constant a' ha').symm)
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all
  have hnZ : Z R a' ≤ normalizer (Z R t) :=
    ((Z R a').le_centralizer.trans (centralizer_le (edge_Z_le_endpoint R ha' ha't))).trans
      (Subgroup.centralizer_le_normalizer _)
  exact commutatorPreimage_normalized _ _ _ _ hnZ
    ((Q_le_stabilizer_of_dist_two R a a' ha hd).trans (Z_normalized R a'))
    (Q R a).le_normalizer
    ((Q_le_adjacent_h R ht hat).trans ((fun _ hx => hx.1) : Q R t ≤ stabilizer R t) |>.trans
      (Z_normalized R t))

omit [Finite M] in
theorem secondarySeed_contains_central_intersection (a t a' : Vertex R) :
    Z R a' ⊓ X R a ≤ secondarySeed R a t a' := by
  apply le_commutatorPreimage inf_le_left
  have hc : ⁅Z R a' ⊓ X R a,Q R a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_right.trans (le_centralizer_iff.mp (Q_le_centralizer_X R a)))
  rw [hc]
  exact bot_le

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
