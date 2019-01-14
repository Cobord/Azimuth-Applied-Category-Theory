{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

data Learner aSet bSet pSet = Learner{
    implementer :: pSet -> aSet -> bSet,
    update :: pSet -> aSet -> bSet -> pSet
    request :: pSet -> aSet -> bSet -> aSet
}

equivalenceLearners :: (qSet -> pSet) -> (Learner aSet bSet pSet) -> (Learner aSet bSet qSet)
equivalenceLearners f learner1 = Learner{implementer=(implementer learner1) f,
                                         update=f_inv ((update learner1) f),
                                         request=(request learner1) f
                                        }

compose_learners :: Learner aSet bSet pSet -> Learner bSet cSet qSet -> Learner aSet cSet (pSet,qSet)

product_learners :: Learner aSet cSet pSet -> Learner cSet dSet qSet -> Learner (aSet,bSet) (cSet,dSet) (pSet,qSet)