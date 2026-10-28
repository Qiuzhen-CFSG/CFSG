module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Core
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions00
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions01
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions02
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions03
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions04
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions05
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions06
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions07
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions08
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions09
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Compositions10
import Mathlib.Tactic.FinCases
/-!
# Correctness of the Rudvalis compressed generators

Induct over the shared-word composition graph. The leaves are the already
certified level-0 and level-1 generator actions; every internal node uses a
kernel-checked table composition. This proves the interpretation needed by
all transition certificates in this block.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
open Theory.GroupTheory
set_option Elab.async false

public theorem sound8 : ∀ x : Fin 4060,
    map8 x.val = (evalWord mixed word8 x).val :=
  comp_sound _ _ _ _ _ sound5 sound6 comp8

public theorem sound9 : ∀ x : Fin 4060,
    map9 x.val = (evalWord mixed word9 x).val :=
  comp_sound _ _ _ _ _ sound7 sound4 comp9

public theorem sound10 : ∀ x : Fin 4060,
    map10 x.val = (evalWord mixed word10 x).val :=
  comp_sound _ _ _ _ _ sound7 sound6 comp10

public theorem sound11 : ∀ x : Fin 4060,
    map11 x.val = (evalWord mixed word11 x).val :=
  comp_sound _ _ _ _ _ sound5 sound4 comp11

public theorem sound12 : ∀ x : Fin 4060,
    map12 x.val = (evalWord mixed word12 x).val :=
  comp_sound _ _ _ _ _ sound1 sound0 comp12

public theorem sound13 : ∀ x : Fin 4060,
    map13 x.val = (evalWord mixed word13 x).val :=
  comp_sound _ _ _ _ _ sound8 sound8 comp13

public theorem sound14 : ∀ x : Fin 4060,
    map14 x.val = (evalWord mixed word14 x).val :=
  comp_sound _ _ _ _ _ sound3 sound0 comp14

public theorem sound15 : ∀ x : Fin 4060,
    map15 x.val = (evalWord mixed word15 x).val :=
  comp_sound _ _ _ _ _ sound10 sound13 comp15

public theorem sound16 : ∀ x : Fin 4060,
    map16 x.val = (evalWord mixed word16 x).val :=
  comp_sound _ _ _ _ _ sound9 sound11 comp16

public theorem sound17 : ∀ x : Fin 4060,
    map17 x.val = (evalWord mixed word17 x).val :=
  comp_sound _ _ _ _ _ sound11 sound9 comp17

public theorem sound18 : ∀ x : Fin 4060,
    map18 x.val = (evalWord mixed word18 x).val :=
  comp_sound _ _ _ _ _ sound10 sound15 comp18

public theorem sound19 : ∀ x : Fin 4060,
    map19 x.val = (evalWord mixed word19 x).val :=
  comp_sound _ _ _ _ _ sound12 sound12 comp19

public theorem sound20 : ∀ x : Fin 4060,
    map20 x.val = (evalWord mixed word20 x).val :=
  comp_sound _ _ _ _ _ sound4 sound9 comp20

public theorem sound21 : ∀ x : Fin 4060,
    map21 x.val = (evalWord mixed word21 x).val :=
  comp_sound _ _ _ _ _ sound14 sound14 comp21

public theorem sound22 : ∀ x : Fin 4060,
    map22 x.val = (evalWord mixed word22 x).val :=
  comp_sound _ _ _ _ _ sound18 sound6 comp22

public theorem sound23 : ∀ x : Fin 4060,
    map23 x.val = (evalWord mixed word23 x).val :=
  comp_sound _ _ _ _ _ sound20 sound16 comp23

public theorem sound24 : ∀ x : Fin 4060,
    map24 x.val = (evalWord mixed word24 x).val :=
  comp_sound _ _ _ _ _ sound1 sound12 comp24

public theorem sound25 : ∀ x : Fin 4060,
    map25 x.val = (evalWord mixed word25 x).val :=
  comp_sound _ _ _ _ _ sound17 sound16 comp25

public theorem sound26 : ∀ x : Fin 4060,
    map26 x.val = (evalWord mixed word26 x).val :=
  comp_sound _ _ _ _ _ sound7 sound10 comp26

public theorem sound27 : ∀ x : Fin 4060,
    map27 x.val = (evalWord mixed word27 x).val :=
  comp_sound _ _ _ _ _ sound8 sound17 comp27

public theorem sound28 : ∀ x : Fin 4060,
    map28 x.val = (evalWord mixed word28 x).val :=
  comp_sound _ _ _ _ _ sound7 sound9 comp28

public theorem sound29 : ∀ x : Fin 4060,
    map29 x.val = (evalWord mixed word29 x).val :=
  comp_sound _ _ _ _ _ sound13 sound9 comp29

public theorem sound30 : ∀ x : Fin 4060,
    map30 x.val = (evalWord mixed word30 x).val :=
  comp_sound _ _ _ _ _ sound8 sound9 comp30

public theorem sound31 : ∀ x : Fin 4060,
    map31 x.val = (evalWord mixed word31 x).val :=
  comp_sound _ _ _ _ _ sound23 sound25 comp31

public theorem sound32 : ∀ x : Fin 4060,
    map32 x.val = (evalWord mixed word32 x).val :=
  comp_sound _ _ _ _ _ sound22 sound30 comp32

public theorem sound33 : ∀ x : Fin 4060,
    map33 x.val = (evalWord mixed word33 x).val :=
  comp_sound _ _ _ _ _ sound1 sound19 comp33

public theorem sound34 : ∀ x : Fin 4060,
    map34 x.val = (evalWord mixed word34 x).val :=
  comp_sound _ _ _ _ _ sound26 sound28 comp34

public theorem sound35 : ∀ x : Fin 4060,
    map35 x.val = (evalWord mixed word35 x).val :=
  comp_sound _ _ _ _ _ sound5 sound29 comp35

public theorem sound36 : ∀ x : Fin 4060,
    map36 x.val = (evalWord mixed word36 x).val :=
  comp_sound _ _ _ _ _ sound5 sound11 comp36

public theorem sound37 : ∀ x : Fin 4060,
    map37 x.val = (evalWord mixed word37 x).val :=
  comp_sound _ _ _ _ _ sound34 sound5 comp37

public theorem sound38 : ∀ x : Fin 4060,
    map38 x.val = (evalWord mixed word38 x).val :=
  comp_sound _ _ _ _ _ sound36 sound35 comp38

public theorem sound39 : ∀ x : Fin 4060,
    map39 x.val = (evalWord mixed word39 x).val :=
  comp_sound _ _ _ _ _ sound38 sound32 comp39

public theorem sound40 : ∀ x : Fin 4060,
    map40 x.val = (evalWord mixed word40 x).val :=
  comp_sound _ _ _ _ _ sound11 sound20 comp40

public theorem sound41 : ∀ x : Fin 4060,
    map41 x.val = (evalWord mixed word41 x).val :=
  comp_sound _ _ _ _ _ sound26 sound39 comp41

public theorem sound42 : ∀ x : Fin 4060,
    map42 x.val = (evalWord mixed word42 x).val :=
  comp_sound _ _ _ _ _ sound18 sound22 comp42

public theorem sound43 : ∀ x : Fin 4060,
    map43 x.val = (evalWord mixed word43 x).val :=
  comp_sound _ _ _ _ _ sound41 sound18 comp43

public theorem sound44 : ∀ x : Fin 4060,
    map44 x.val = (evalWord mixed word44 x).val :=
  comp_sound _ _ _ _ _ sound8 sound15 comp44

public theorem sound45 : ∀ x : Fin 4060,
    map45 x.val = (evalWord mixed word45 x).val :=
  comp_sound _ _ _ _ _ sound27 sound23 comp45

public theorem sound46 : ∀ x : Fin 4060,
    map46 x.val = (evalWord mixed word46 x).val :=
  comp_sound _ _ _ _ _ sound24 sound14 comp46

public theorem sound47 : ∀ x : Fin 4060,
    map47 x.val = (evalWord mixed word47 x).val :=
  comp_sound _ _ _ _ _ sound40 sound31 comp47

public theorem sound48 : ∀ x : Fin 4060,
    map48 x.val = (evalWord mixed word48 x).val :=
  comp_sound _ _ _ _ _ sound37 sound27 comp48

public theorem sound49 : ∀ x : Fin 4060,
    map49 x.val = (evalWord mixed word49 x).val :=
  comp_sound _ _ _ _ _ sound43 sound42 comp49

public theorem sound50 : ∀ x : Fin 4060,
    map50 x.val = (evalWord mixed word50 x).val :=
  comp_sound _ _ _ _ _ sound12 sound14 comp50

public theorem sound51 : ∀ x : Fin 4060,
    map51 x.val = (evalWord mixed word51 x).val :=
  comp_sound _ _ _ _ _ sound21 sound14 comp51

public theorem sound52 : ∀ x : Fin 4060,
    map52 x.val = (evalWord mixed word52 x).val :=
  comp_sound _ _ _ _ _ sound49 sound47 comp52

public theorem sound53 : ∀ x : Fin 4060,
    map53 x.val = (evalWord mixed word53 x).val :=
  comp_sound _ _ _ _ _ sound10 sound28 comp53

public theorem sound54 : ∀ x : Fin 4060,
    map54 x.val = (evalWord mixed word54 x).val :=
  comp_sound _ _ _ _ _ sound45 sound27 comp54

public theorem sound55 : ∀ x : Fin 4060,
    map55 x.val = (evalWord mixed word55 x).val :=
  comp_sound _ _ _ _ _ sound54 sound48 comp55

public theorem sound56 : ∀ x : Fin 4060,
    map56 x.val = (evalWord mixed word56 x).val :=
  comp_sound _ _ _ _ _ sound29 sound52 comp56

public theorem sound57 : ∀ x : Fin 4060,
    map57 x.val = (evalWord mixed word57 x).val :=
  comp_sound _ _ _ _ _ sound55 sound7 comp57

public theorem sound58 : ∀ x : Fin 4060,
    map58 x.val = (evalWord mixed word58 x).val :=
  comp_sound _ _ _ _ _ sound12 sound24 comp58

public theorem sound59 : ∀ x : Fin 4060,
    map59 x.val = (evalWord mixed word59 x).val :=
  comp_sound _ _ _ _ _ sound34 sound44 comp59

public theorem sound60 : ∀ x : Fin 4060,
    map60 x.val = (evalWord mixed word60 x).val :=
  comp_sound _ _ _ _ _ sound1 sound1 comp60

public theorem sound61 : ∀ x : Fin 4060,
    map61 x.val = (evalWord mixed word61 x).val :=
  comp_sound _ _ _ _ _ sound25 sound57 comp61

public theorem sound62 : ∀ x : Fin 4060,
    map62 x.val = (evalWord mixed word62 x).val :=
  comp_sound _ _ _ _ _ sound32 sound31 comp62

public theorem sound63 : ∀ x : Fin 4060,
    map63 x.val = (evalWord mixed word63 x).val :=
  comp_sound _ _ _ _ _ sound12 sound21 comp63

public theorem sound64 : ∀ x : Fin 4060,
    map64 x.val = (evalWord mixed word64 x).val :=
  comp_sound _ _ _ _ _ sound24 sound21 comp64

public theorem sound65 : ∀ x : Fin 4060,
    map65 x.val = (evalWord mixed word65 x).val :=
  comp_sound _ _ _ _ _ sound19 sound19 comp65

public theorem sound66 : ∀ x : Fin 4060,
    map66 x.val = (evalWord mixed word66 x).val :=
  comp_sound _ _ _ _ _ sound12 sound33 comp66

public theorem sound67 : ∀ x : Fin 4060,
    map67 x.val = (evalWord mixed word67 x).val :=
  comp_sound _ _ _ _ _ sound0 sound14 comp67

public theorem sound68 : ∀ x : Fin 4060,
    map68 x.val = (evalWord mixed word68 x).val :=
  comp_sound _ _ _ _ _ sound6 sound9 comp68

public theorem sound69 : ∀ x : Fin 4060,
    map69 x.val = (evalWord mixed word69 x).val :=
  comp_sound _ _ _ _ _ sound33 sound14 comp69

public theorem sound70 : ∀ x : Fin 4060,
    map70 x.val = (evalWord mixed word70 x).val :=
  comp_sound _ _ _ _ _ sound18 sound62 comp70

public theorem sound71 : ∀ x : Fin 4060,
    map71 x.val = (evalWord mixed word71 x).val :=
  comp_sound _ _ _ _ _ sound53 sound35 comp71

public theorem sound72 : ∀ x : Fin 4060,
    map72 x.val = (evalWord mixed word72 x).val :=
  comp_sound _ _ _ _ _ sound68 sound31 comp72

public theorem sound73 : ∀ x : Fin 4060,
    map73 x.val = (evalWord mixed word73 x).val :=
  comp_sound _ _ _ _ _ sound72 sound61 comp73

public theorem sound74 : ∀ x : Fin 4060,
    map74 x.val = (evalWord mixed word74 x).val :=
  comp_sound _ _ _ _ _ sound53 sound44 comp74

public theorem sound75 : ∀ x : Fin 4060,
    map75 x.val = (evalWord mixed word75 x).val :=
  comp_sound _ _ _ _ _ sound24 sound24 comp75

public theorem sound76 : ∀ x : Fin 4060,
    map76 x.val = (evalWord mixed word76 x).val :=
  comp_sound _ _ _ _ _ sound51 sound3 comp76

public theorem sound77 : ∀ x : Fin 4060,
    map77 x.val = (evalWord mixed word77 x).val :=
  comp_sound _ _ _ _ _ sound19 sound14 comp77

public theorem sound78 : ∀ x : Fin 4060,
    map78 x.val = (evalWord mixed word78 x).val :=
  comp_sound _ _ _ _ _ sound19 sound12 comp78

public theorem sound79 : ∀ x : Fin 4060,
    map79 x.val = (evalWord mixed word79 x).val :=
  comp_sound _ _ _ _ _ sound4 sound11 comp79

public theorem sound80 : ∀ x : Fin 4060,
    map80 x.val = (evalWord mixed word80 x).val :=
  comp_sound _ _ _ _ _ sound5 sound25 comp80

public theorem sound81 : ∀ x : Fin 4060,
    map81 x.val = (evalWord mixed word81 x).val :=
  comp_sound _ _ _ _ _ sound70 sound56 comp81

public theorem sound82 : ∀ x : Fin 4060,
    map82 x.val = (evalWord mixed word82 x).val :=
  comp_sound _ _ _ _ _ sound24 sound33 comp82

public theorem sound83 : ∀ x : Fin 4060,
    map83 x.val = (evalWord mixed word83 x).val :=
  comp_sound _ _ _ _ _ sound34 sound35 comp83

public theorem sound84 : ∀ x : Fin 4060,
    map84 x.val = (evalWord mixed word84 x).val :=
  comp_sound _ _ _ _ _ sound6 sound30 comp84

public theorem sound85 : ∀ x : Fin 4060,
    map85 x.val = (evalWord mixed word85 x).val :=
  comp_sound _ _ _ _ _ sound22 sound17 comp85

public theorem sound86 : ∀ x : Fin 4060,
    map86 x.val = (evalWord mixed word86 x).val :=
  comp_sound _ _ _ _ _ sound8 sound73 comp86

public theorem sound87 : ∀ x : Fin 4060,
    map87 x.val = (evalWord mixed word87 x).val :=
  comp_sound _ _ _ _ _ sound0 sound21 comp87

public theorem sound88 : ∀ x : Fin 4060,
    map88 x.val = (evalWord mixed word88 x).val :=
  comp_sound _ _ _ _ _ sound43 sound7 comp88

public theorem sound89 : ∀ x : Fin 4060,
    map89 x.val = (evalWord mixed word89 x).val :=
  comp_sound _ _ _ _ _ sound33 sound33 comp89

public theorem sound90 : ∀ x : Fin 4060,
    map90 x.val = (evalWord mixed word90 x).val :=
  comp_sound _ _ _ _ _ sound0 sound19 comp90

public theorem sound91 : ∀ x : Fin 4060,
    map91 x.val = (evalWord mixed word91 x).val :=
  comp_sound _ _ _ _ _ sound6 sound17 comp91

public theorem sound92 : ∀ x : Fin 4060,
    map92 x.val = (evalWord mixed word92 x).val :=
  comp_sound _ _ _ _ _ sound33 sound19 comp92

public theorem sound93 : ∀ x : Fin 4060,
    map93 x.val = (evalWord mixed word93 x).val :=
  comp_sound _ _ _ _ _ sound7 sound15 comp93

public theorem sound94 : ∀ x : Fin 4060,
    map94 x.val = (evalWord mixed word94 x).val :=
  comp_sound _ _ _ _ _ sound25 sound25 comp94

public theorem sound95 : ∀ x : Fin 4060,
    map95 x.val = (evalWord mixed word95 x).val :=
  comp_sound _ _ _ _ _ sound19 sound3 comp95

public theorem gen_sound (i : Fin 96) (x : Fin 4060) :
    gen i x.val = (evalWord mixed (word i) x).val := by
  fin_cases i
  · exact sound0 x
  · exact sound1 x
  · exact sound2 x
  · exact sound3 x
  · exact sound4 x
  · exact sound5 x
  · exact sound6 x
  · exact sound7 x
  · exact sound8 x
  · exact sound9 x
  · exact sound10 x
  · exact sound11 x
  · exact sound12 x
  · exact sound13 x
  · exact sound14 x
  · exact sound15 x
  · exact sound16 x
  · exact sound17 x
  · exact sound18 x
  · exact sound19 x
  · exact sound20 x
  · exact sound21 x
  · exact sound22 x
  · exact sound23 x
  · exact sound24 x
  · exact sound25 x
  · exact sound26 x
  · exact sound27 x
  · exact sound28 x
  · exact sound29 x
  · exact sound30 x
  · exact sound31 x
  · exact sound32 x
  · exact sound33 x
  · exact sound34 x
  · exact sound35 x
  · exact sound36 x
  · exact sound37 x
  · exact sound38 x
  · exact sound39 x
  · exact sound40 x
  · exact sound41 x
  · exact sound42 x
  · exact sound43 x
  · exact sound44 x
  · exact sound45 x
  · exact sound46 x
  · exact sound47 x
  · exact sound48 x
  · exact sound49 x
  · exact sound50 x
  · exact sound51 x
  · exact sound52 x
  · exact sound53 x
  · exact sound54 x
  · exact sound55 x
  · exact sound56 x
  · exact sound57 x
  · exact sound58 x
  · exact sound59 x
  · exact sound60 x
  · exact sound61 x
  · exact sound62 x
  · exact sound63 x
  · exact sound64 x
  · exact sound65 x
  · exact sound66 x
  · exact sound67 x
  · exact sound68 x
  · exact sound69 x
  · exact sound70 x
  · exact sound71 x
  · exact sound72 x
  · exact sound73 x
  · exact sound74 x
  · exact sound75 x
  · exact sound76 x
  · exact sound77 x
  · exact sound78 x
  · exact sound79 x
  · exact sound80 x
  · exact sound81 x
  · exact sound82 x
  · exact sound83 x
  · exact sound84 x
  · exact sound85 x
  · exact sound86 x
  · exact sound87 x
  · exact sound88 x
  · exact sound89 x
  · exact sound90 x
  · exact sound91 x
  · exact sound92 x
  · exact sound93 x
  · exact sound94 x
  · exact sound95 x

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
