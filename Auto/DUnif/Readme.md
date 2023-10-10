__Debugging__
* To debug unification procedure, use
  ```
  set_option trace.auto.dunif.debug true
  ```
* To enable advanced debugging functionality, use
  ```
  set_option auto.dunif.dbgOn true
  ```
* The ```contains <k>``` option of ```dapply``` and ```drefl``` is useless when ```auto.dunif.dbgOn``` is ```false```, because we do not push parent clause and can't check ```contains``` when ```auto.dunif.dbgOn``` is ```false```.