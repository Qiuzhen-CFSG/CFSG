module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.BlockData
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction

/-!
# Fixed finite coordinates for the unitary exterior-square comparison

Over F₃, the sum of six squares is a nonsplit six-dimensional quadratic form.
Its nonisotropic one-spaces have 252 representatives, chosen by the smaller
ternary code of v and -v. They embed in Λ²(F₉⁴) as
`(u,v,w,conj(w),-conj(v),conj(u))`, for three pairs of ternary coordinates.
The Pfaffian restricts to the sum of their three norms, hence to six squares.

This module fixes the coordinates shared by the action construction and the
independent finite generator comparison. It asserts neither a unitary action
nor generation by the ATLAS-derived block permutations.
Source: the exterior-square realization of twisted A₃/D₃, GLS3 §2.7;
Aschbacher–Smith I.1.4(5), p.408. The imported exterior-square API is the
attributed ATLAS port; see its copyright header and LICENSES/ATLAS.txt.
-/

@[expose] public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
open Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary

abbrev Vector := Fin 6 → ZMod 3
abbrev Index := BlockAction.Block

def norm (v : Vector) : ZMod 3 := ∑ i, v i ^ 2

def vectorCode (v : Vector) : Nat := ∑ i, (v i).val * 3 ^ i.val

def coordinates (i : Index) : Vector :=
  fun k => ((((186062107201672483080810330955501561248485407597967679445776462966512924752959517737753347923617842455546456922546368268572044327366040773621298586029930026471338436071489130431902349235653873825593455025441159701673842225262791829807160547657417147743867274206146434899916730784767538429174858250407552794733659113446728789726242001181278858709607760918370081081982745567906553411252462944995298480628446074631872257997582076970350660537288849458919478808023311050773848234497035288703432542873044879986077002237626658715248384520129073246464983884943073359423002335664235426571564846697948355142412633260999880972913973497462505283007668567028626050370361100190993373743362570114353714960544740441981881824723349911673610414528993407991491381081365129726977 : Nat) >>> (10 * i.val)) % 1024) / 3 ^ k.val : Nat)

def indexOf (v : Vector) : Index :=
  ⟨((40988664087852863474932078342893435446158063730764502715806508600127548677124698480205397318798233022438281686195719134588716304346475334238507009425604971361601320280587999341192943147353249297820194070128464633127702713774815256364368788666606211830178941852613458830609475509726599065157794065110502070002121557114436545621048283821223026822211944236282309975680272638215323968366777376788259914481519421674467655667328514441898814502891111957889278733491673287017258787691768293434842183098201922320985018963400041736355307179536226712606870716003105184771844004786389933537564419266392418233477239631592368527806688876137412610707177026556864046160086417289754970413192183054713383147432362471773011709481495529690339218610015324822025849293404814233485967694690204976347621844800395187125972432185415012155279936782290766464473520087836991629790089022089709606541156477092037436041525661114144576241726132267079263085209522389624491987949921069799343939952860291456769173909146726950298343764643637868379108501151946340847484145764413154840715344051346061987273030401643186122890182863163077397869574326925620050680159560770143379278483337950893811068528074278753136005835539790087638673826813408947471815257086089905945612995666439303691755133317991289272291429144787913849812520726910019876346728353179298063649758222990512256757790717429418551449366986837731868588154333466777405692957654439297521882366747704224674816673699100661467604012865685048750397398024806335294199046531463854322414026780992321041420353285555062847961960793965955571201913164916305052628075307623803816897214760113268395839624532256267772369518944838343619785642442036618607255380973783337296949846367414524624917899140550956558576034731138416682571566708037435523072 : Nat) >>> (8 * vectorCode v)) % 256 % 252,
    Nat.mod_lt _ (by decide)⟩

set_option Elab.async false

theorem coordinates_norm_ne_zero : ∀ i, norm (coordinates i) ≠ 0 := by decide +kernel

theorem indexOf_coordinates : ∀ i, indexOf (coordinates i) = i := by decide +kernel

theorem indexOf_neg_coordinates : ∀ i, indexOf (-coordinates i) = i := by decide +kernel

/-- Every nonisotropic vector has precisely the displayed projective sign class. -/
theorem coordinates_complete : ∀ v : Vector, norm v ≠ 0 →
    v = coordinates (indexOf v) ∨ v = -coordinates (indexOf v) := by decide +kernel

/-- Equality up to sign cannot identify different indices. -/
theorem coordinates_sign_injective {i j : Index}
    (h : coordinates i = coordinates j ∨ coordinates i = -coordinates j) : i = j := by
  rcases h with h | h
  · simpa only [indexOf_coordinates] using congrArg indexOf h
  · simpa only [indexOf_coordinates, indexOf_neg_coordinates] using congrArg indexOf h

/-- The three complex coordinates of a real six-vector. -/
def pair (v : Vector) (i j : Fin 6) : FiniteField.Nine := ⟨v i, v j⟩

/-- The fixed real form of the exterior square, in lexicographic minor order. -/
def bivector (v : Vector) : Six FiniteField.Nine :=
  ![pair v 0 1, pair v 2 3, pair v 4 5,
    star (pair v 4 5), -star (pair v 2 3), star (pair v 0 1)]

theorem bivector_injective : Function.Injective bivector := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  change pair v 0 1 = pair w 0 1 at h0
  change pair v 2 3 = pair w 2 3 at h1
  change pair v 4 5 = pair w 4 5 at h2
  ext i
  fin_cases i
  · exact congrArg QuadraticAlgebra.re h0
  · exact congrArg QuadraticAlgebra.im h0
  · exact congrArg QuadraticAlgebra.re h1
  · exact congrArg QuadraticAlgebra.im h1
  · exact congrArg QuadraticAlgebra.re h2
  · exact congrArg QuadraticAlgebra.im h2

theorem bivector_neg (v : Vector) : bivector (-v) = -bivector v := by
  have pair_neg (i j : Fin 6) : pair (-v) i j = -pair v i j := rfl
  funext i
  fin_cases i <;> simp [bivector, pair_neg]

/-- The displayed real form has the intended quadratic values. -/
theorem pfaffian_bivector (v : Vector) :
    pfaffian (bivector v) = (algebraMap (ZMod 3) FiniteField.Nine) (norm v) := by
  have h : ∀ v : Vector,
      pfaffian (bivector v) = (algebraMap (ZMod 3) FiniteField.Nine) (norm v) := by
    decide +kernel
  exact h v

/-- The bivector line indexed by one of the 252 nonisotropic points. -/
def point (i : Index) : Six FiniteField.Nine := bivector (coordinates i)

theorem point_sign_injective {i j : Index}
    (h : point i = point j ∨ point i = -point j) : i = j := by
  apply coordinates_sign_injective
  rcases h with h | h
  · exact Or.inl (bivector_injective h)
  · exact Or.inr (bivector_injective (h.trans (bivector_neg _).symm))

/-- The literal formula required of the independently constructed projective action.
It retains the natural SU projection and the actual exterior compound matrix. -/
def RealizesExterior (ρ : UnitaryFourThree.Carrier 4 →* Equiv.Perm Index) : Prop :=
  ∀ (g : (UnitaryFourThree.form 4).specialSubgroup) (i : Index),
    exteriorMap g.val.val (point i) = point (ρ (UnitaryFourThree.project 4 g) i) ∨
    exteriorMap g.val.val (point i) = -point (ρ (UnitaryFourThree.project 4 g) i)

/-- Two sign choices for the same exterior vector determine the same point. -/
theorem point_eq_of_sign_choices {w : Six FiniteField.Nine} {i j : Index}
    (hi : w = point i ∨ w = -point i) (hj : w = point j ∨ w = -point j) : i = j := by
  apply point_sign_injective
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact Or.inl (hi.symm.trans hj)
  · exact Or.inr (hi.symm.trans hj)
  · exact Or.inr (by simpa only [neg_neg] using congrArg Neg.neg (hi.symm.trans hj))
  · exact Or.inl (neg_injective (hi.symm.trans hj))

/-- The independent generator comparison must supply actual unitary matrices,
a common point labeling, and generation of the literal projective SU image.
No group-family name or order is a field of this witness. -/
structure GeneratorComparison where
  first : (UnitaryFourThree.form 4).specialSubgroup
  second : (UnitaryFourThree.form 4).specialSubgroup
  labeling : BlockAction.Block ≃ Index
  generates : Subgroup.closure
    ({UnitaryFourThree.project 4 first, UnitaryFourThree.project 4 second} :
      Set (UnitaryFourThree.Carrier 4)) = ⊤
  first_action : ∀ i,
    exteriorMap first.val.val (point (labeling i)) =
        point (labeling (BlockAction.blockA i)) ∨
    exteriorMap first.val.val (point (labeling i)) =
        -point (labeling (BlockAction.blockA i))
  second_action : ∀ i,
    exteriorMap second.val.val (point (labeling i)) =
        point (labeling (BlockAction.blockB i)) ∨
    exteriorMap second.val.val (point (labeling i)) =
        -point (labeling (BlockAction.blockB i))

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
